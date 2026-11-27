# Smooth-vector density in the full cuspidal Hilbert space

`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeFullAEL2SmoothDensity`
proves `GroupSchemeFullAEL2SmoothDensityStatement` in every universe `u`. Its
type is exactly that proposition. The hypotheses are the statement's own: an
affine, locally finite-type connected reductive group scheme `G` over a number
field, the structural `ParabolicDynamicStatement` `hPD`, the split central
torus data `T`, `i`, `hi`, `I`, `e`, `hc`, and right invariance of Haar
measure on the norm-one subgroup. No split or quasi-split hypothesis on `G`
occurs.

The space `C` is the unchanged `fullAEL2CuspidalSubmodule`. It is the closed
subspace of `Lp ℂ 2 (positiveRationalQuotientHaarMeasure F G T i)` whose
periods along every actual proper rational parabolic converge absolutely
almost everywhere and vanish. Its actions are the restricted
`fullAEL2CuspidalInfiniteRightAction` and `fullAEL2CuspidalFiniteRightAction`.

## The projection

The proof fixes the completion scalar instances and the atlas
`InfiniteAdelicGroupPoints.reductiveChartedSpace F G hG`, as in the statement.
It then uses the subtype-valued orthogonal projection
`fullAEL2CuspidalOrthogonalProjection F G hPD hG T i hi I e hc`, a continuous
linear map `Lp ℂ 2 μQ →L[ℂ] C`, where `μQ` is the positive rational quotient
Haar measure. Three facts about it are used.

- It is surjective. By `fullAEL2CuspidalOrthogonalProjection_inclusion` it
  sends the underlying ambient vector of each `φ : C` back to `φ`.
- It intertwines the infinite actions. By
  `fullAEL2CuspidalOrthogonalProjection_infiniteRightAction` it carries
  `haarQuotientL2InfiniteRightAction` to `fullAEL2CuspidalInfiniteRightAction`.
  So `Langlands.Global.RestrictionSplitCentre.isSmoothVector_of_intertwining`
  sends every ambient archimedean smooth vector to a vector of
  `Langlands.Archimedean.smoothVectors` for the cusp action.
- It intertwines the finite actions. The full adelic law
  `fullAEL2CuspidalOrthogonalProjection_rightAction`, at the image
  `ofFinite F G b` of a finite point `b`, carries
  `haarQuotientL2FiniteRightAction` to `fullAEL2CuspidalFiniteRightAction`.
  So `Langlands.Global.RestrictionSplitCentre.isSmoothVector_of_finiteIntertwining`
  shows that an open subgroup fixing an ambient vector also fixes its
  projection, which is `Langlands.IsSmoothVector` for the cusp finite action.

## Density

`groupSchemeQuotientL2SmoothDensity`, the proof of
`GroupSchemeQuotientL2SmoothDensityStatement`, gives two dense subsets of the
ambient space: the archimedean smooth vectors, and the archimedean smooth
vectors that are also finitely smooth. A continuous map with dense range
carries dense sets to dense sets (`DenseRange.dense_image`). The projection is
continuous and surjective, so the image of each set is dense in `C`. By the
two intertwining facts above, the first image lies in the cusp archimedean
smooth vectors and the second lies in the cusp vectors that are smooth for
both actions. Density passes to a superset (`Dense.mono`), which gives both
conjuncts.

## Provenance

The quotient convention follows Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), §2.6, (2.19)–(2.22), printed pp. 68–69 (PDF
pp. 85–86), `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`. The
argument is not taken from that source. It derives the cuspidal result from
the ambient density theorem `groupSchemeQuotientL2SmoothDensity` and the
equivariance of the orthogonal projection onto the cusp space.
