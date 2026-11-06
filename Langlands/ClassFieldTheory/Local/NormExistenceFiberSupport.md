# Compact fibers for local norms and power maps

This support module isolates the compact-fiber input to the local norm-subgroup
existence argument. The Prop-valued assertion `CompactLocalNormAndPowerFibers`
uses arbitrary prime and independent field universes, actual determinant norms,
and the supplied field topologies.

The generic kernel lemma proves that a continuous group homomorphism into a
Hausdorff group has compact fibers when its kernel lies in a compact subgroup.
A nonempty fiber is contained in the translate of that subgroup by one chosen
preimage. Continuity makes the fiber closed, so the compact translate contains
it as a compact closed subset. Empty fibers are compact as well.

The second generic lemma lifts an element through a downward directed nonempty
family of closed subgroups if it has a preimage in each subgroup and its fiber
is compact. Intersect each subgroup with the fiber and apply the directed
compact intersection theorem. This is the compactness step in the universal
norm lifting argument; its arithmetic hypotheses remain the caller's obligation.

For an actual local norm, the published relative norm-order identity places
its kernel in the integral units. For a nonzero power map, torsion-freeness of
the integer normalized-order group places the power kernel in the integral
units. The already published compactness of integral units then supplies both
compact-fiber results. The final theorem proves the packaged assertion.

This is derived internal support. Its local inputs are the published
`ord_relative_norm_units_eq_zero_iff`, `mem_unitFiltration_zero_of_ord_eq_zero`,
`unitFiltration_zero`, `isCompact_unitFiltration`, and continuity of `localNorm`.
The generic compact intersection lemma is Mathlib's directed Cantor theorem.
These lemmas supply the topological role of proper norm maps in the classical
universal-norm argument without asserting full properness of these maps.
