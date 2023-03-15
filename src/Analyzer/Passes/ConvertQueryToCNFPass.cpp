#include <Analyzer/Passes/ConvertQueryToCNFPass.h>

#include <Analyzer/InDepthQueryTreeVisitor.h>
#include <Analyzer/FunctionNode.h>
#include <Analyzer/TableNode.h>
#include <Analyzer/TableFunctionNode.h>
#include <Analyzer/Passes/CNF.h>
#include <Analyzer/Utils.h>
#include "Storages/ConstraintsDescription.h"
#include "Storages/ProjectionsDescription.h"
#include "Storages/StorageSnapshot.h"

namespace DB
{

namespace
{

bool isLogicalFunction(const FunctionNode & function_node)
{
    const std::string_view name = function_node.getFunctionName();
    return name == "and" || name == "or" || name == "not";
}

std::optional<Analyzer::CNF> tryConvertQueryToCNF(const QueryTreeNodePtr & node, const ContextPtr & context)
{
    auto * function_node = node->as<FunctionNode>();

    if (!function_node || !isLogicalFunction(*function_node))
        return std::nullopt;

    auto cnf_form = Analyzer::CNF::tryBuildCNF(node, context);
    if (!cnf_form)
        return std::nullopt;

    cnf_form->pushNotIntoFunctions(context);
    return cnf_form;
}

enum class MatchState : uint8_t
{
    FULL_MATCH, /// a = b
    PARTIAL_MATCH, /// a = not b
    NONE,
};

MatchState match(const Analyzer::CNF::AtomicFormula & a, const Analyzer::CNF::AtomicFormula & b)
{
    using enum MatchState;
    if (a.node_with_hash.hash != b.node_with_hash.hash)
        return NONE;

    return a.negative == b.negative ? FULL_MATCH : PARTIAL_MATCH;
}

bool checkIfGroupAlwaysTrueFullMatch(const Analyzer::CNF::OrGroup & group, const ConstraintsDescription & constraints_description, const ContextPtr & context)
{
    /// We have constraints in CNF.
    /// CNF is always true => Each OR group in CNF is always true.
    /// So, we try to check whether we have al least one OR group from CNF as subset in our group.
    /// If we've found one then our group is always true too.

    const auto & query_tree_constraint = constraints_description.getQueryTreeData(context);
    const auto & constraints_data = query_tree_constraint.getConstraintData();
    std::vector<size_t> found(constraints_data.size());
    for (size_t i = 0; i < constraints_data.size(); ++i)
        found[i] = constraints_data[i].size();

    for (const auto & atom : group)
    {
        const auto constraint_atom_ids = query_tree_constraint.getAtomIds(atom.node_with_hash);
        if (constraint_atom_ids)
        {
            const auto constraint_atoms = query_tree_constraint.getAtomsById(*constraint_atom_ids);
            for (size_t i = 0; i < constraint_atoms.size(); ++i)
            {
                if (match(constraint_atoms[i], atom) == MatchState::FULL_MATCH)
                {
                    if ((--found[(*constraint_atom_ids)[i].group_id]) == 0)
                        return true;
                }
            }
        }
    }
    return false;
}

bool checkIfGroupAlwaysTrueGraph(const Analyzer::CNF::OrGroup & group, const ComparisonGraph<QueryTreeNodePtr> & graph)
{
    /// We try to find at least one atom that is always true by using comparison graph.
    for (const auto & atom : group)
    {
        const auto * function_node = atom.node_with_hash.node->as<FunctionNode>();
        if (function_node)
        {
            const auto & arguments = function_node->getArguments().getNodes();
            if (arguments.size() == 2)
            {
                const auto expected = ComparisonGraph<QueryTreeNodePtr>::atomToCompareResult(atom);
                if (graph.isAlwaysCompare(expected, arguments[0], arguments[1]))
                    return true;
            }
        }
    }

    return false;
}

bool checkIfAtomAlwaysFalseFullMatch(const Analyzer::CNF::AtomicFormula & atom, const ConstraintsDescription & constraints_description, const ContextPtr & context)
{
    const auto & query_tree_constraint = constraints_description.getQueryTreeData(context);
    const auto constraint_atom_ids = query_tree_constraint.getAtomIds(atom.node_with_hash);
    if (constraint_atom_ids)
    {
        for (const auto & constraint_atom : query_tree_constraint.getAtomsById(*constraint_atom_ids))
        {
            const auto match_result = match(constraint_atom, atom);
            if (match_result == MatchState::PARTIAL_MATCH)
                return true;
        }
    }

    return false;
}

bool checkIfAtomAlwaysFalseGraph(const Analyzer::CNF::AtomicFormula & atom, const ComparisonGraph<QueryTreeNodePtr> & graph)
{
    const auto * function_node = atom.node_with_hash.node->as<FunctionNode>();
    if (!function_node)
        return false;

    const auto & arguments = function_node->getArguments().getNodes();
    if (arguments.size() != 2)
        return false;

    /// TODO: special support for !=
    const auto expected = ComparisonGraph<QueryTreeNodePtr>::atomToCompareResult(atom);
    return !graph.isPossibleCompare(expected, arguments[0], arguments[1]);
}

void replaceToConstants(QueryTreeNodePtr & term, const ComparisonGraph<QueryTreeNodePtr> & graph)
{
    const auto equal_constant = graph.getEqualConst(term);
    if (equal_constant)
    {
        term = (*equal_constant)->clone();
        return;
    }

    for (auto & child : term->getChildren())
        replaceToConstants(child, graph);
}

Analyzer::CNF::AtomicFormula replaceTermsToConstants(const Analyzer::CNF::AtomicFormula & atom, const ComparisonGraph<QueryTreeNodePtr> & graph)
{
    auto node = atom.node_with_hash.node->clone();
    replaceToConstants(node, graph);
    return {atom.negative, std::move(node)};
}

void optimizeWithConstraints(Analyzer::CNF & cnf, const StorageMetadataPtr & metadata_snapshot, const ContextPtr & context)
{
    const auto & constraints = metadata_snapshot->getConstraints();
    const auto & query_tree_constraint = constraints.getQueryTreeData(context);
    const auto & compare_graph = query_tree_constraint.getGraph();
    cnf.filterAlwaysTrueGroups([&](const auto & group)
       {
           /// remove always true groups from CNF
           return !checkIfGroupAlwaysTrueFullMatch(group, constraints, context) && !checkIfGroupAlwaysTrueGraph(group, compare_graph);
       })
       .filterAlwaysFalseAtoms([&](const Analyzer::CNF::AtomicFormula & atom)
       {
           /// remove always false atoms from CNF
           return !checkIfAtomAlwaysFalseFullMatch(atom, constraints, context) && !checkIfAtomAlwaysFalseGraph(atom, compare_graph);
       })
       .transformAtoms([&](const auto & atom)
       {
           return replaceTermsToConstants(atom, compare_graph);
       })
       .reduce();
}

void optimizeNode(QueryTreeNodePtr & node, const QueryTreeNodes & table_expressions, const ContextPtr & context)
{
    const auto & settings = context->getSettingsRef();

    auto cnf = tryConvertQueryToCNF(node, context);
    if (!cnf)
        return;

    if (settings.optimize_using_constraints)
    {
        cnf->pullNotOutFunctions(context);

        for (const auto & table_expression : table_expressions)
        {
            StorageSnapshotPtr storage_snapshot{nullptr};
            if (auto * table_node = table_expression->as<TableNode>())
                storage_snapshot = table_node->getStorageSnapshot();
            else if (auto * table_function_node = table_expression->as<TableFunctionNode>())
                storage_snapshot = table_function_node->getStorageSnapshot();

            if (!storage_snapshot || !storage_snapshot->metadata)
                continue;

            optimizeWithConstraints(*cnf, storage_snapshot->metadata, context);
        }

        cnf->pushNotIntoFunctions(context);
    }

    auto new_node = cnf->toQueryTree(context);
    if (!new_node)
        return;

    node = std::move(new_node);
}

class ConvertQueryToCNFVisitor : public InDepthQueryTreeVisitorWithContext<ConvertQueryToCNFVisitor>
{
public:
    using Base = InDepthQueryTreeVisitorWithContext<ConvertQueryToCNFVisitor>;
    using Base::Base;

    static bool needChildVisit(VisitQueryTreeNodeType & parent, VisitQueryTreeNodeType &)
    {
        return parent->as<QueryNode>() == nullptr;
    }

    void visitImpl(QueryTreeNodePtr & node)
    {
        auto * query_node = node->as<QueryNode>();
        if (!query_node)
            return;

        auto table_expressions = extractTableExpressions(query_node->getJoinTree());

        if (query_node->hasWhere())
            optimizeNode(query_node->getWhere(), table_expressions, getContext());

        if (query_node->hasPrewhere())
            optimizeNode(query_node->getPrewhere(), table_expressions, getContext());
    }
};

}

void ConvertQueryToCNFPass::run(QueryTreeNodePtr query_tree_node, ContextPtr context)
{
    const auto & settings = context->getSettingsRef();
    if (!settings.convert_query_to_cnf)
        return;

    ConvertQueryToCNFVisitor visitor(std::move(context));
    visitor.visit(query_tree_node);
}

}
