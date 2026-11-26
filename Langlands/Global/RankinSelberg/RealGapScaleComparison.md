# Integrating the two scaled comparisons on the normalized real gap charts

This module is the real counterpart of the Library's `ComplexGapScaleComparison`.

* `squareIntegral_reflection`: let `B` be a uniform real Whittaker intertwiner of the character list
  `fs.map character` at `a`, and let the leading square tests have a finite-dimensional span of left
  translates by the orthogonal group. Let `F` be the ordinary separated kernel with square weight
  `ordinaryWeight [c] es a √|a| 1 rate L (c₀ ·)` and `Fm` the mixed separated kernel with weight
  `reflectedWeight ([c].map dualBlock) (es.map dualBlock) rate L (c₀⁻¹ ·)`, and let
  `m₀ = D.measure.prod (ordinaryChartMeasure t q a D.groupHaar κ)` (so `η₁ = D.groupHaar`). If `F` and `Fm`
  are both integrable for `m₀`, then `∫ F ∂m₀ = c₀ · ∫ Fm ∂m₀`. The two kernels themselves are not compared
  pointwise: the identity holds only after integration over the leading group.
* `lowerIntegral_reflection`: if every pair of values of uniform intertwiners `B` (rank `t+1+q`, at `−a`)
  and `B'` (rank `t`, at `a`) has `HasRealPairNormalizedGrowth ds es dds ees eb sc hsc sign` for
  `realUnequalIntegral` and `realUnequalDualIntegral … (−a)`, then for any Haar measures `η₁`, `κ` and any
  square weight `k₂`: if the mixed separated kernel `Fm` with lower weight `ordinaryWeight ds es eb … (b ·)`
  is integrable for `m₀ = D.measure.prod (ordinaryChartMeasure t q a η₁ κ)` and the dual separated kernel
  `Fd` with `reflectedWeight dds ees … (b⁻¹ ·)` is integrable for
  `md = D.measure.prod (dualChartMeasure t q a η₁ κ)`, then
  `detCharacter c⁻¹ (w_(q+1)) · ∫ Fm ∂m₀ = b · ∫ Fd ∂md`.

`RealGapScaleComparisonStatement` (proved by `realGapScaleComparison`) composes the two integrated
identities: with `η₁ = D.groupHaar`, `detCharacter c⁻¹ (w_(q+1)) · ∫ F ∂m₀ = (b c₀) · ∫ Fd ∂md` for the
ordinary and dual separated kernels with the two scaled weight pairs, when `F` and `Fm` are integrable for
`m₀` and `Fd` is integrable for `md`.

## Proof

`realGapLeadingHaar` splits the outer measure into `η₁` and the retained measure, and by Fubini (using the
integrability of `F` and `Fm`) each integral over `m₀` is an integral over the quotient and retained
variables of an inner integral over the leading group. At a fixed quotient representative and retained
point both kernels are a common factor times a leading-group integrand, and `realGapSquareWeighted` for
`Φ = leadingRestriction C T.leading` (Proposition 4.4 integrated against the Whittaker function `B v`)
shows that the inner integral for `F` is `c₀` times the one for `Fm`.
For the lower comparison the product measure is permuted so that the smaller quotient and its complementary
rectangle are innermost (`measurePreserving_lowerEquiv`, with `RealJacquet.selfDualMeasure_neg`), and
`realUnequalWeightedTranslation` applies to the right translates `ρ(C⁻¹)(B v)` and `ρ(z)(B' v')`.

This implements the two comparisons of Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.3,
(10.7)–(10.10), pp. 75–76 (the square step by Proposition 4.4, p. 31), with the pairs of §10.4, p. 77.
