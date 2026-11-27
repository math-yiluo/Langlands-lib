# Smooth density on the restriction split-centre quotient

`Langlands.Global.RestrictionSplitCentre.quotientL2SmoothDensity` proves
`Langlands.Global.RestrictionSplitCentre.QuotientL2SmoothDensityStatement`
from `Langlands.Automorphic.GroupSchemeRestrictionQuotientL2SmoothDensityStatement`.
Its type is exactly that proposition. In the published setting of the
restriction split-centre quotient `[G] = Quotient F G S j` with its Haar
quotient measure `quotientHaarMeasure F G S j`, it shows:

- the vectors of `L²([G])` that are real smooth for the infinite adelic
  right action `rationalQuotientL2InfiniteRightAction` are dense;
- the vectors that are real smooth for that action and also fixed by an
  open subgroup of the finite adelic points under
  `rationalQuotientL2FiniteRightAction` are dense.

All hypotheses of the proposition are kept as stated: the split-centre
comparison `subgroup F G S j = imageSubgroup F T G i`, injectivity and
finite-index range of `characterRestrict i`, centrality of `i`, the
split-torus hypothesis on `T`, right invariance of Haar measure on the
norm-one subgroup, and the quotient right invariance `hInv'`. No split or
quasi-split hypothesis on `G` occurs.

## Proof

1. The proof introduces the binders of the proposition and fixes the same two
   local instances as the statement: the `RCLike` structure
   `InfinitePlaceGroupPoints.completionRCLike F v` on each archimedean
   completion and the atlas
   `InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG` on the infinite
   adelic points. The model with corners is
   `𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F hG.smoothDimension)`.
2. The hypothesis `IsSplitTorus T.toGrp` is by definition the existence of
   a finite type `I` and an isomorphism `e : T.toGrp ≅ splitTorus _ I`. The
   proof destructures it and turns `Finite I` into a `Fintype I` instance
   with `Fintype.ofFinite`.
3. With these coordinates,
   `Langlands.Automorphic.GroupSchemeFunctions.groupSchemeQuotientL2SmoothDensity`,
   the proof of `GroupSchemeQuotientL2SmoothDensityStatement`, gives both
   density results on the positive-torus quotient
   `Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)` for the actions
   `haarQuotientL2InfiniteRightAction F G T i hi I e hc` and
   `haarQuotientL2FiniteRightAction F G T i hi I e hc`.
4. The module `GroupSchemeRestrictionQuotientL2SmoothVectors` compares the two
   quotients through the linear isometric equivalence
   `quotientL2Equiv F G h`, which intertwines the infinite and the finite
   actions on both sides. Its theorems `dense_smoothVectors_iff` and
   `dense_biSmoothVectors_iff` state that density of the real smooth
   vectors, and of the simultaneously smooth vectors, on `L²([G])` is
   equivalent to the corresponding density on the positive-torus quotient.
   The reverse implications of these two equivalences, applied to the two
   results of step 3, give the two conjuncts of the proposition.

Both sides use the same atlas on the infinite adelic points, so the smooth
vectors on the two quotients are taken for the same manifold structure. The
proof depends only on `propext`, `Classical.choice` and `Quot.sound`.

## Provenance

The quotient `[G] = A_G G(F) \ G(A_F)` is that of Getz–Hahn, *An
Introduction to Automorphic Representations* (2024), §2.6, (2.19)–(2.22),
printed pp. 68–69 (PDF pp. 85–86),
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The density assertion is not taken from that source. It is an internal
consequence of Library results: the positive-torus density theorem
`groupSchemeQuotientL2SmoothDensity` and the transport of smooth vectors and
density along the measure-preserving quotient comparison `quotientL2Equiv`.
