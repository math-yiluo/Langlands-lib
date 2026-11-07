# Smooth-vector density in `L²([G])`

Author: Worker 112.

`Langlands.Global.RestrictionSplitCentre.QuotientL2SmoothDensityStatement`
asks for two density results in `L²` of the restriction split-centre quotient
`RestrictionSplitCentre.Quotient F G S j`. This quotient has the shape
`[G] = A_G G(F) \ G(A_F)` of Getz--Hahn (2.20)--(2.21)
(`getz-hahn-2024-automorphic-representations`, printed pp. 68--69). The space
is `Lp ℂ 2 (quotientHaarMeasure F G S j)` with the published canonical
quotient measure. The proposition is the `[G]` counterpart of Worker 116's
published positive-torus
`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeQuotientL2SmoothDensityStatement`.

## Hypotheses

The proposition quantifies over:

- a number field `F : Type`, and a group scheme `G` over `Spec F` whose
  underlying scheme is affine and locally of finite type, with
  `hG : IsConnectedReductive G`;
- a commutative group scheme `S` over `ℚ` and
  `j : S.toGrp ⟶ AffineWeil.groupScheme ℚ F G`, which define the published
  quotient `Quotient F G S j`;
- a commutative group scheme `T` over `F` and `i : T.toGrp ⟶ G` with
  `subgroup F G S j = imageSubgroup F T G i`, injective `characterRestrict i`
  with finite-index range, `IsCentral i` and `IsSplitTorus T.toGrp`;
- right invariance of Haar measure on `normOneSubgroup F G` (an instance
  argument), and any proof `hInv'` of
  `QuotientRightInvariant F G (quotientHaarMeasure F G S j)`.

The four hypotheses on `T` and `i` do not occur in the conclusion, so they
are anonymous binders. They are the hypotheses of the
published comparison `quotientL2Equiv` between `L²([G])` and the positive-torus
quotient `L²`, and of the published joint continuity of the right action on
`L²([G])`. They are a sufficient setting for the intended proof below. The
proposition does not claim that they are needed. There is no split or
quasi-split hypothesis on `G`.

## Conclusion

The two local instances are the published ones of the positive statement:
the `RCLike` structure `InfinitePlaceGroupPoints.completionRCLike F v` on each
archimedean completion, and the atlas
`InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG` on the infinite
adelic points, modelled on
`InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension`.

Let `Sm` be the published real-manifold smooth-vector subspace
`Langlands.Archimedean.smoothVectors` of the infinite action
`rationalQuotientL2InfiniteRightAction F G (quotientHaarMeasure F G S j) hInv'`
from `GroupSchemeRestrictionQuotientL2InfiniteAction`. A vector lies in `Sm`
when its orbit map is `C^∞` on this manifold. The proposition asserts:

- `Sm` is dense in `L²([G])`;
- the vectors of `Sm` that are also `Langlands.IsSmoothVector` for the
  published finite action `rationalQuotientL2FiniteRightAction` are dense in
  `L²([G])`. The finite condition means that some open subgroup of the finite
  adelic points fixes the vector.

## Intended proof

This module states the proposition and contains no proof. The intended proof
transports Worker 116's positive-torus statement along the published
isometric equivalence `quotientL2Equiv F G h`, where `h` is the hypothesis
`subgroup F G S j = imageSubgroup F T G i`. It carries the positive-torus
infinite and finite actions to those on `L²([G])`. A linear isometric
equivalence that intertwines the actions maps smooth vectors onto smooth
vectors and dense sets onto dense sets. The split-torus coordinates `I`, `e`
of the positive statement come from the hypothesis `IsSplitTorus T.toGrp`. This route needs a proof of the
positive statement; the present module supplies neither proof.

## Provenance and scope

The quotient `[G]` is Getz--Hahn (2.20)--(2.21). The density assertion is the
`[G]` form of the published internal positive-torus statement; no theorem of
Getz--Hahn is cited for it. The proposition supplies no pointwise smooth
representative, finite volume, cuspidal analogue, admissibility,
compactness, trace or spectral decomposition.
