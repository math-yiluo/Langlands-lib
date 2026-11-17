# Actual restriction and equivariant stable projections

For a matrix representation over any field, `IsEquivariantProjection ρ V P`
means that the matrix of the ground-field linear endomorphism `P` intertwines
`ρ` with itself on every affine test, that `P` takes values in `V`, and that
`P` fixes `V`. The last two conditions use Mathlib's `LinearMap.IsProj`.

The restriction lemmas preserve all-test stable subspaces, intertwiners and
equivariant projections along arbitrary actual group-scheme morphisms. Restriction
along an isomorphism also reflects stable subspaces. No point-surjectivity,
smoothness, reducedness, finite-type or affineness hypothesis is needed.

`intertwines_iff_linearFunctional_mulVec` characterizes actual intertwiners by
commuting with every linear-functional coefficient of every affine translate.
The forward implication is the existing coefficient-intertwining theorem.
For the converse, linear functionals separate elements of any test algebra as
a vector space over the field. This recovers the affine vector identity;
applying it to standard basis vectors proves the required matrix equality.

`isEquivariantProjection_of_isCompl` constructs an equivariant projection from
two stable complementary subspaces. A vector is written as a sum of components
in those subspaces. Both the affine coefficient operation and the projection
are additive; stability of the two subspaces lets the projection retain the
first coefficient and kill the second. The coefficient characterization then
proves actual equivariance. Conversely an equivariant projection has a stable
kernel, because kernels of intertwiners are inverse images of the stable zero
subspace. Mathlib's projection theorem makes this kernel complementary to `V`.
`exists_stable_complement_iff_exists_equivariantProjection` combines the two
constructions for any stable `V`.

## Provenance

This is internal derived infrastructure for actual group-scheme representations.
It implements the elementary invariant-complement and equivariant-projection
correspondence used in Milne, *Algebraic Groups* (2022 corrected reprint),
Proposition 4.17, printed p. 90, and Exercise 4-3, printed p. 97. The registered
source is `milne-2022-algebraic-groups`, SHA-256
`f2ddd8fa4d263085f173934664b246007a2c0bd539739b7c82de39bfb5d21f40`.
The official errata snapshot, registered as
`milne-2022-algebraic-groups-errata-2026-11-04`, was read in full and has no entry
for these passages. The coefficient test and restriction helpers are derived
from the Library's existing actual representation and all-test stability APIs.
This module does not perform finite-quotient averaging or prove Nagata's theorem.

The restriction and kernel helpers are reused from `Chevalley/ActualRepresentationExtension` and `Reductive/CovariantFrobeniusProducts`; they retain their existing declarations.
