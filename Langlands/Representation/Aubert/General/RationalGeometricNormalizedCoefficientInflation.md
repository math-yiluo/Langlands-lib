# Inflation of the original normalized coefficient from the common Levi

This internal contribution extends the actual coefficient-character
factorization from the literal common Levi to the full target intersection.
Its entry definition is `geometricNormalizedCompactInflatedCharacter`, and
`geometricNormalizedCompactCharacter_eq_inflated` identifies it with the
original normalized compact coefficient character. Both original epsilon
corrections and the remaining endpoint ratio are retained.

For the original rational-point subgroups, put

- `MI = levi i ν I`, `MJ = levi i ν J`, `PJ = parabolic i ν J`, and
  `UJ = unipotent i ν J`;
- `K = (MI ∩ n PJ n⁻¹).subgroupOf MI`;
- `Lt = (MI ∩ n MJ n⁻¹).subgroupOf MI`;
- `Rt = (MI ∩ n UJ n⁻¹).subgroupOf MI` and `Rk = Rt.subgroupOf K`.

Every intersection above is the existing `geometricTargetIntersection`, not
an isomorphic replacement. The inclusion `c : Lt →* K` is the original
`geometricCommonLeviInTarget`, and `π : K →* Lt` is the actual projection of
`hTarget : GeometricTargetDecomposition …`. The original coefficient map is
`p = geometricCoefficientLeviMap … hTarget`; it composes `π` with the
original inverse-conjugation equivalence into the source common Levi.

Write `η` for `geometricNormalizedCompactCharacter`. On all of `K` its
existing definition is

`η = (complex(positiveHalf(δU)) / complex(δD)) * χp`,

where `δU` and `δD` are the original compact radical and correction moduli,
and `χp` is the original inducing positive half pulled back through `p`.

## Radical triviality and projection

`isLimitOfCompactSubgroups_geometricTargetRadical` derives the compact-limit
property for `Rt` from the same property for the original inducing radical
`UJ`. It applies the published
`isLimitOfCompactSubgroups_geometricSourceIntersection` with `n⁻¹` and the
closed subgroup `MI`. Unfolding the two literal intersection definitions and
`inv_inv` gives exactly `Rt`.

For `geometricNormalizedCompactCharacter_eq_one_on_radical`, closedness of
`MI` and `PJ` makes `K` closed inside `MI`. The existing
`isLimitOfCompactSubgroups_subgroupOf` therefore gives the compact-limit
property for `Rk`. Both original positive modulus characters `δU` and `δD`
have open kernels. Applying
`positiveCharacter_eq_one_on_compactLimit` makes them equal to one on every
`r : Rk`, and hence also makes their canonical positive half and complex
embeddings equal to one. The actual projection kills `Rk` by
`hTarget.projection_eq_one_iff`, so `p r = 1` and the inducing half is also
one. Substitution in the original formula proves `η r = 1`.

`geometricNormalizedCompactCharacter_eq_projection` proves the equality of
monoid homomorphisms

`η = ((η.comp c).comp π)`.

The implemented proof first establishes the group-theoretic argument for an
abstract semidirect decomposition. For `x` in its parabolic,
`(c (π x))⁻¹ * x` belongs to the nested radical by
`projection_inv_mul_mem`. A character trivial on that radical sends this
element to one. Multiplicativity and `inv_mul_eq_one` give
`η x = η (c (π x))`. The rational-point specialization uses equality of the
original inclusion `c` with `Subgroup.inclusion hTarget.levi_le`; their
underlying elements agree and their containment proofs are irrelevant.
Doing the subgroup argument before specialization avoids repeated kernel
reduction of the large rational-point projection expression.

## The inflated character

The definition is exactly

`((geometricEpsilonOne * geometricEpsilonTwo) * endpointRatio).comp π`,

with the original epsilons and the existing
`geometricNormalizedCompactEndpointRatioCharacter`. The latter is the
canonical positive half of the target intersection radical modulus times
the inverse half of the source intersection radical modulus, restricted
to the literal common Levi. The final theorem substitutes
`geometricNormalizedCompactCharacter_commonLevi_eq_epsilonProduct` into
the projection equality. It proves equality with the original `η` on every
full-intersection element, without assuming any balance between distinct
radical moduli.

## Scope and provenance

The field universe is arbitrary. The compact-limit argument uses the
original rational-point topological space and nonarchimedean group, closed
`MI` and `PJ`, and the compact-limit property for `UJ`. The Haar-character
lemmas also retain local compactness and closedness of the original `UI`
and `UJ`. The final epsilon-product identification additionally retains
second countability, `StandardCocharacterStatement`, connected reductivity,
maximal split torus, generic cocharacter, point-normalizer comparison,
closed `PI` and `MJ`, and continuity of both original projections. No
minimality, splitness, characteristic-zero or positive-rank condition is
introduced. These are character results and impose no representation-carrier
universe constraint.

The provenance is internal: the existing literal-intersection compact-limit,
open-kernel, semidirect projection and common-Levi character results imply
these claims by subgroup restriction and multiplicative character algebra.
No new translation from literature is claimed. This contribution does not
prove whole-common-Levi balance, remove either epsilon, identify the
normalized representation endpoints, compare compact and full induction,
construct the ordered filtration or prove
`RationalGeometricK0ExpansionStatement`. Those host-task obligations remain.
