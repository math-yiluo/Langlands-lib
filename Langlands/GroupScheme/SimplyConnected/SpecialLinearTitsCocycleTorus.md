# Diagonal weights and split-torus transport over a field extension

Author: Worker 187, Task 6023.

This internal helper provides character evaluation and cover-point identities
for the diagonal-torus conclusions of `SpecialLinearTitsCocycleStatement`.
It does not construct the presentation asserted by that statement.

For any finite index type `n`, pivot `p`, scheme `S`, and index `i`,
`SpecialLinear.diagonalWeight p S i` is the sum of the coordinate characters
with the integer coefficients `weightCoord p i`. The source is the actual
split commutative group scheme indexed by the universe lift of `OffPivot p`.
`pointsEquiv_diagonalWeight` evaluates this character as `torusWeights` on
every relative test. The proof evaluates a sum as a product and each integer
multiple as the corresponding power. Consequently,
`coe_pointsEquiv_diagonalTorus_weights` expresses every point of the standard
diagonal torus in the special-linear matrix model as the diagonal of these
character values, over every commutative ring.

The shared `LocalGroupIso.coverPointsEquiv_comp`, imported from
`LocalGroupIsoBaseChangeEquivalence`, says that cover-point projection
commutes with any group-scheme homomorphism. Its proof uses naturality of the
base-change point equivalence. For an actual local group isomorphism `e`,
`coverPointsEquiv_toBaseChangeIso_inv` identifies the inverse of its recovered
base-change isomorphism with the inverse local value at the chosen cover
point. This follows from inverse naturality and the point formula for the
recovered isomorphism. Finally, `Gm.pointsEquiv_coverPointsEquiv` says that the
multiplicative-group comparison preserves the unit on each relative test;
the proof uses the base-change unit comparison and pullback along the
identity of the test scheme.

The cover identities allow arbitrary base schemes and actual relative
tests. No restriction to rational points, characteristic, positive torus
rank, or reduced test schemes is introduced.

Provenance: derived directly from the published diagonal torus, character
lattice, base change and local-isomorphism constructions. No classification
result is assumed.
