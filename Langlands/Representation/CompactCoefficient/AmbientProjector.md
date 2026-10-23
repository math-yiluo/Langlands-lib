# Ambient total compact-isotypic projectors

This internal construction promotes a pointwise finite sum of intrinsic
compact-isotypic projectors on a normal subgroup to an actual intertwiner for
the ambient group. It derives the result from the published
`IsotypicTransport`, `ConditionalProjection`, `OrthogonalProjectorFamily`,
`TotalProjector` and `PointwiseProjectorSum` interfaces. It does not assert
existence of the components or their pointwise finite support.

## Covariance of the total

`CompactCoefficientClass.pointwiseFiniteSum_isotypic_covariant` takes groups
`G` and `H` with topologies, a continuous multiplicative equivalence
`e : H ≃ₜ* G`, smooth complex representations `A` of `G` and `B` of `H`,
and families `P` and `Q` indexed by their respective compact-coefficient
classes at a common representative-carrier universe. The group universes,
representative-carrier universe and two ambient-carrier universes are independent.

For each family the hypotheses are:

- Its values have finite support on each vector.
- Each component is idempotent.
- Each component range is the intrinsic isotypic subrepresentation.
- Each component kernel is the intrinsic annihilator subrepresentation.

For every actual intertwiner `f` from the pullback of `A` along `e` to `B`,
the conclusion is

`(sum Q) (f v) = f ((sum P) v)`.

The proof first regards `P` as a family of endomorphisms of the pulled-back
representation. The published intrinsic component covariance identifies its
transported component with the component of `Q` indexed by
`CompactCoefficientClass.pullbackEquiv e`. The published covariance theorem
for pointwise finite sums then reindexes using this actual equivalence of
classes. Orthogonality is not needed for this covariance statement.

## Normal-subgroup conjugation

`SmoothRep.restrictSubgroup N A` is the same vector space with action
`A.representation.comp N.subtype`. Smoothness is proved by the published
continuous-pullback theorem and continuity of the subgroup inclusion. The
subgroup need not be open or normal for this definition.
`SmoothRep.restrictSubgroupMap` retains the linear map of any actual ambient
intertwiner.

For a topological group `G` and a normal subgroup `N`,
`SmoothRep.normalSubgroupInverseConjugation N g` is the actual continuous
multiplicative equivalence of `N` given by

`n ↦ g⁻¹ n g`.

Its inverse is `n ↦ g n g⁻¹`. Normality proves that both maps take values
in `N`; the group laws prove multiplicativity and the inverse identities.
Continuity follows from multiplication by constants and the subspace topology
on `N`.

`SmoothRep.restrictionConjugationMap N A g` is the linear action of `g`.
It intertwines the restriction pulled back by the preceding inverse
conjugation with the original restriction. Its equivariance is exactly

`ρ(g) ρ(g⁻¹ n g) = ρ(n) ρ(g)`.

## Actual ambient endomorphism

`CompactCoefficientClass.ambientTotalProjector` takes a smooth complex
representation `A` of a topological group `G`, a normal subgroup `N`, and
a family `P` of endomorphisms of the restriction. Its index consists of all
compact-coefficient classes of `N` at the specified representative-carrier
universe. The same four explicit hypotheses from the covariance theorem are
required. No topology or dimension condition on `A` is introduced.

`pointwiseFiniteSum_commutes_ambient` applies total covariance to the actual
inverse-conjugation equivalence and the action intertwiner constructed above.
It proves that the subgroup total commutes with every `ρ(g)`. This supplies
the equivariance field of `ambientTotalProjector`, whose linear map is
exactly the original pointwise finite sum.

With pairwise ordered orthogonality supplied as an additional hypothesis,
`ambientTotalProjector_idempotent` proves idempotence.
`ambientTotalProjector_range` and `ambientTotalProjector_ker` identify its
underlying range and kernel submodules with those of the intrinsic total
isotypic and total annihilator subrepresentations of the restriction. These
are equalities of underlying submodules because the subrepresentations on
the two sides have different acting groups. The proofs use the published
range and kernel laws for the same pointwise finite sum, then rewrite the
component ranges and kernels.

`ambientTotalProjectors_natural` takes two such families on ambient
representations with independent carrier universes. Restricting any actual
ambient intertwiner, applying component naturality, and taking the pointwise
sum gives naturality of the actual ambient totals. This law does not require
orthogonality.

The module supplies no analytic splitting, fixed-level finiteness, compactness
of the total image, or identity on every compact-coefficient object. Those
remain separate inputs to a quasicuspidal decomposition application.
