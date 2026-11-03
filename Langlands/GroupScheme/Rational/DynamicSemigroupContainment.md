# Factorization through the positive Dynamic representative

Over any field and at arbitrary universe `u`, let `G` be affine and locally of
finite type, let `S` be a split torus with a homomorphism `i : S → G`, and let
`ν` be any cocharacter of `S`. For a smooth connected closed subgroup functor `F`
stable under this torus action, suppose that its actual tangent image is contained
in the weight span with strictly positive pairing against `ν`.
`dynamicUnipotentFactorOfTangent` constructs the morphism from any representative
`j : H → G` of `F` to the actual affine representative of
`Dynamic.unipotent (ν ≫ i)`. Its composite with the Dynamic inclusion is `j`,
as proved by `dynamicUnipotentFactorOfTangent_comp`.

The construction is internally derived from existing Library definitions and
proofs. It does not translate a new assertion from the literature. The ambient
group need not be smooth or connected, and the conclusion holds on every test
scheme. Smoothness and connectedness are required of the closed subgroup `F`.
No realization or uniqueness premise for a generated semigroup subgroup is used.

The main containment theorem
`le_dynamicUnipotent_of_tangentSubmodule_le` chooses a smooth connected closed
representative of `F` and induces the original torus action on it using
[`RepresentedAction`](../RepresentedAction.md). Restricting
along `ν` gives a multiplicative-group action `a` on this representative.
Its inclusion into `G` is equivariant for `a` and conjugation along `ν ≫ i`.
The closed equivariant reflection theorem from
[`ActionFunctoriality`](../Dynamic/ActionFunctoriality.md) identifies `a.unipotent`
with the inverse image of the original Dynamic unipotent functor.

The action `a` has a smooth closed unipotent representative by
[`ActionAffineRepresentability`](../Dynamic/ActionAffineRepresentability.md).
For every actual Lie point of the chosen representative of `F`, its image in
`G` lies in the positive weight span by the tangent bound. The adapter in
[`CocharacterWeightSums`](CocharacterWeightSums.md) and the published
[`Dynamic Lie theorem`](../Dynamic/LieProof.md) place that image in the actual
Dynamic unipotent functor. Equivariant reflection therefore places the original
Lie point in `a.unipotent`. A lift to the action-unipotent representative is
itself a Lie point, because its closed inclusion is a monomorphism.

Consequently that smooth closed representative has full Lie image in the smooth
connected group representing `F`. The published full-Lie equality theorem from
[`SubgroupEqualityProof`](../Lie/SubgroupEqualityProof.md) makes its range the
whole group. Connectedness of the action-unipotent representative is not needed.
Reflection then proves `F ≤ Dynamic.unipotent (ν ≫ i)` on every test.

`positive_generator_le_dynamicUnipotent` specializes this result to every
`IsSemigroupGenerator` for the positive pairing region. The support-to-tangent
equivalence from [`SemigroupWeightSupport`](SemigroupWeightSupport.md) supplies
the tangent bound. Finally the universal morphism between representatives of
included subgroup functors, from
[`RepresentedLieUniqueness`](RepresentedLieUniqueness.md), constructs
`dynamicUnipotentFactorOfTangent` and proves its factorization equation.

Worker 1284 authored the induced-action argument and factorization construction.
Worker 1301 authored the cocharacter weight-span adapters used by the proof.
This module supplies positive reverse containment; it does not by itself prove
the full three-part `DynamicSemigroupComparisonStatement`.
