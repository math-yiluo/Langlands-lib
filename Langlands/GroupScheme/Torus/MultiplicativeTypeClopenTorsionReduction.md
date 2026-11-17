# Clopen torsion comparison, conditional on torsion determination

Worker 508.

This internal reduction takes the existing proposition
`MultiplicativeTypeTorsionDeterminationStatement` as an explicit input. It
does not assert or import a proof of that proposition.

Let `j : G → H` be an open and closed embedding of commutative group schemes
over an arbitrary scheme `S`. Assume `G` has relative multiplicative type and
every geometric fibre of `H` has field-level multiplicative type.
`FibralClopen.isoOfEqualGeometricTorsionOrders` constructs an actual
isomorphism `G ≅ H` when the geometric torsion coordinate dimensions of `G`
and `H` agree at every point for every natural `n > 0`. Its forward map is `j`.

For each geometric fibre, the published separably-closed-field splitting
theorem turns field-level multiplicative type into relative diagonalizability
and hence relative multiplicative type. Both positive torsion schemes are
finite by the actual relative torsion geometry theorem. The canonical
torsion restriction of the closed embedding is an isomorphism by
`TorsionOrderComparison.torsionIsoOfFinrankEq`. Thus every point of the target
fibre killed by a positive integer factors through the fibre subgroup. Part
(4.9) of the supplied torsion-determination proposition makes that subgroup
the entire geometric fibre.

Every point of the total target lifts to its geometric fibre. Invertibility
on that fibre therefore makes the total clopen map surjective. A flat,
surjective, quasi-compact monomorphism is an isomorphism; this yields the
actual group-scheme comparison.

`isoOfLocallyConstantTorsionOrders` specializes this construction to a
preconnected base. It only requires local constancy of the target geometric
torsion orders and equality with the subgroup orders at one given point.
The subgroup orders are already locally constant because `G` has relative
multiplicative type. Both functions are constant on the preconnected base,
so equality propagates from the given point.

The coordinate dimensions, scalar structures and natural-number quantifiers
are exactly those of the published fibral criterion. There are no smoothness,
Noetherian, reducedness, global affineness or characteristic assumptions.
The conditional dependence on torsion determination remains an explicit
parameter in every main comparison. This module proves neither the
diagonalizable lifting assertion nor the full fibral criterion.
