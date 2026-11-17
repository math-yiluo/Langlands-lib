# Twisted-stable chambers over the maximal unramified extension

`Langlands.Geometry.Building.unramifiedTwistedChamber` proves exactly
`UnramifiedTwistedChamberStatement.{u}`, at arbitrary universe `u`, with no
additional hypothesis. For the group, torus, apartment and centralizer data in
the statement, every cocycle trivial on the fixing subgroup of a finite
intermediate field admits a chamber stable under the twisted action of every
element of `Aut(inertiaFixedField F / F)`.

The proof applies the published theorem
`unramifiedTwistedChamber_of_metric` to two published unconditional inputs:

- `unramifiedBuildingMetric` supplies a complete nonpositively curved metric
  on the original reduced building, invariant under the rational-point and
  coefficient actions.
- `unramifiedTwistedChamberThroughFixedPoint` supplies a twisted-stable
  chamber through any twisted-fixed point, with its closure witnesses.

The reduction first invokes `unramifiedTwistedFixedPoint_of_metric`. The
finite-level cocycle gives a finite orbit for its twisted action, so the
bounded-action fixed-point theorem gives a fixed point. Applying the second
input there and retaining its chamber and stability clauses yields precisely
the target. All these steps use the same original building and coefficient
action.

This is an internal composition of published Library results. It introduces
no new source-defined statement; the mathematical provenance of the metric,
fixed-point and residual arguments is documented in the imported modules.
The target statement and every Lean/Markdown pair it imports are unchanged.
The proof uses no proof of any of the five downstream simply connected chamber
or cocycle-vanishing statements prohibited by the task.

The accompanying compatibility edit gives the three local instances in
`IntegerBuildingFacetCentroids` explicit names so that the metric and residual
proof imports can coexist. It preserves their types, defining terms and local
status and changes no mathematical assertion.
