# The infinite adelic action on `L²([G])`

Author: Worker 112.

The published module `GroupSchemeRestrictionQuotientL2` constructs the right
regular representation `rationalQuotientL2RightAction` on `L²` of the
restriction split-centre quotient `RestrictionSplitCentre.Quotient F G S j`.
This quotient has the shape `[G] = A_G G(F) \ G(A_F)` of Getz--Hahn
(2.20)--(2.21) (`getz-hahn-2024-automorphic-representations`, printed
pp. 68--69). The published `GroupSchemeRestrictionQuotientL2Continuity`
bundles that action by bounded operators and proves that it is jointly
continuous for the canonical measure. The published
`GroupSchemeRestrictionQuotientL2FiniteAverage` restricts it to the finite
adelic points and averages it over compact open subgroups.

The present module restricts the same bounded action to the infinite adelic
points `G(F ⊗ ℝ)` along the published continuous homomorphism
`AdelicGroupPoints.ofInfinite`. It proves the elementary properties of this
restriction. It is the `[G]` counterpart of the published positive-torus
module `GroupSchemeQuotientL2InfiniteAction`. It also proves that the published
`L²` identification `quotientL2Equiv` carries the positive-torus infinite
action to the new one. No new `L²` space, measure or action on the quotient is
chosen.

## Data and hypotheses

- `F : Type` is a number field.
- `G` is a group scheme over `Spec F` whose underlying scheme is affine and
  locally of finite type.
- `S` is a commutative group scheme over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`.
- In the first section, `measureQ` is any measure on `Quotient F G S j`, and
  `hInv : QuotientRightInvariant F G measureQ` states that every actual right
  translation preserves it.
- From the second section on, the measure is the canonical
  `quotientHaarMeasure F G S j`, with any proof `hInv'` of its right
  invariance. Every result holds for whichever proof is given. In addition,
  `T` is a commutative group scheme over `F` with `i : T.toGrp ⟶ G` and
  `h : subgroup F G S j = imageSubgroup F T G i`. Also `characterRestrict i`
  is injective (`hi`) with finite-index range, `hc : IsCentral i`,
  `hT : IsSplitTorus T.toGrp`, and Haar measure on `normOneSubgroup F G` is
  right invariant (an instance argument). These are the hypotheses of the
  published joint continuity theorem.
- No connected reductivity and no smooth manifold structure is assumed.

## Any right-invariant measure

- `rationalQuotientL2InfiniteRightAction F G measureQ hInv` is the published
  bounded action `rationalQuotientL2BoundedRightAction` composed with
  `AdelicGroupPoints.ofInfinite F G`. It is a monoid homomorphism from
  `InfiniteAdelicGroupPoints F G` to the bounded operators on
  `Lp ℂ 2 measureQ`. By `rationalQuotientL2InfiniteRightAction_apply`, the
  operator of `a` is `rationalQuotientL2RightAction (ofInfinite a)`; this holds
  by definition.
- `norm_rationalQuotientL2InfiniteRightAction`: every operator preserves the
  `L²` norm.
- `rationalQuotientL2InfiniteFinite_commute`: the operator of an infinite
  point `a` commutes with the operator of a finite point `b` under the
  published `rationalQuotientL2FiniteRightAction`. The proof applies the
  bounded action to the published `AdelicGroupPoints.factors_commute`, which
  says that `ofInfinite a` and `ofFinite b` commute in `G(A_F)`.

## The canonical measure

- `continuous_rationalQuotientL2InfiniteOrbit`: for every `φ`, the orbit
  `a ↦ π∞ a φ` is continuous on the infinite adelic points. It is the published
  continuous orbit map `rationalQuotientL2OrbitMap` composed with the
  continuous map `ofInfinite`.
- `rationalQuotientL2InfiniteOrbit_aestronglyMeasurable`: for every measure
  `ν` on the infinite adelic points, the orbit is almost everywhere strongly
  measurable. A continuous map is strongly measurable here, because the
  infinite adelic points are second countable and `L²` is metrizable.
- `quotientL2Equiv_infiniteRightAction`: for any splitting coordinates
  `I`, `e` of `T`, the published `quotientL2Equiv F G h` carries the published
  positive-torus `haarQuotientL2InfiniteRightAction F G T i hi I e hc a` to the
  operator of `a` on `[G]`. This is the published `quotientL2Equiv_rightAction`
  at `ofInfinite a`.
- `rationalQuotientL2FiniteAverage_infiniteRightAction`: let `K` be a compact
  open subgroup of the finite adelic points. The published average
  `rationalQuotientL2FiniteAverage` over `K` commutes with every infinite
  operator. The proof applies the published `compactIsometricAverage_intertwiner`
  to the infinite operator, using the commutation above. `K` carries the
  subgroup topology and its Borel structure, through the published local
  instances of `GroupSchemeQuotientL2FiniteAverage`.

## Split components

The section `SplitComponents` replaces `h`, `hc`, `hT` and `hInv'` by
`hj : IsSplitComponent j` and `hs : IsSplitComponent i`, keeping `hi` with
finite-index range and norm-one right invariance. It uses the published
`subgroup_eq_of_splitComponents` and
`quotientHaarMeasure_rightInvariant_of_splitComponents`.

- `splitComponentL2InfiniteRightAction` is the infinite action for this right
  invariance proof, with `_apply` in terms of the published
  `splitComponentL2RightAction`.
- `continuous_splitComponentL2InfiniteOrbit`: infinite orbits are continuous.
- `splitComponentL2Equiv_infiniteRightAction`: the published
  `splitComponentL2Equiv` carries the positive-torus infinite action, for any
  splitting coordinates of `T`, to `splitComponentL2InfiniteRightAction`.
- `splitComponentL2FiniteAverage_infiniteRightAction`: the published
  `splitComponentL2FiniteAverage` over a compact open `K` commutes with the
  infinite action.

## Scope

The module constructs no smooth structure and proves no density of smooth
vectors (archimedean or finite). It proves no finite volume, admissibility,
decomposition or spectral statement. The published positive-torus
`GroupSchemeQuotientL2SmoothDensityStatement` is stated for the
positive-torus quotient. A `[G]` counterpart of that statement is not
formulated here.

## Provenance

This is an internal restriction of the published bounded action on
`L²([G])` along the published inclusion of the infinite adelic points. It
follows the published positive-torus `GroupSchemeQuotientL2InfiniteAction` of
Worker 116. The proofs use the published `AdelicGroupPoints.factors_commute`,
`rationalQuotientL2OrbitMap`, `quotientL2Equiv_rightAction` and
`compactIsometricAverage_intertwiner`, and Mathlib's
`Continuous.stronglyMeasurable`. No external theorem is asserted.
