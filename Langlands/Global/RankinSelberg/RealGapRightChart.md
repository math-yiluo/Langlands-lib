# The real consecutive-block right Haar chart

This module is the real counterpart of the Library's `ComplexGapRightChart`.

`consecutiveRightChart k q ((g₁, g₂), Y), u) = u · diag(1, g₂) · packedTail Y 1 · diag(g₁, 1)` on
`((GL_k(ℝ) × GL_{q+1}(ℝ)) × Mat_{k×(q+1)}(ℝ)) × O(k + q + 1)` (`measurable_consecutiveRightChart`), and
`consecutiveTailWeight k q g₂ = |det g₂|^{-k}` (`measurable_consecutiveTailWeight`).
`rightTail_eq_consecutive` identifies the general two-block right-tail factor `rightTail` of
`RealTwoBlockRightHaar` at the block sizes `k` and `(k + q + 1) - k` with the consecutive block formula,
transported along `tailSize : q + 1 = (k + q + 1) - k` by `groupCongr` and `rectangleCongr`.
`map_withDensity_comp` moves a density pulled back along a measurable map through the image measure.

`RealGapRightChartStatement` (proved by `realGapRightChart`): for `0 < k`, an additive Haar measure
`μ` on `ℝ`, Haar measures `η` on `GL_{k+q+1}(ℝ)`, `η₁` on `GL_k(ℝ)`, `η₂` on `GL_{q+1}(ℝ)`, and a Haar
measure `κ` on the orthogonal group invariant under inversion, there is `c > 0` with

`η = c • map consecutiveRightChart ((((η₁ × η₂) × rectangularMeasure μ k (q + 1)) × κ)
  .withDensity (|det g₂|^{-k}))`.

The proof applies `RealTwoBlockHaar.realTwoBlockRightHaar` at the sizes `k` and `(k + q + 1) - k`
with the transported tail measure `η₂.map groupCongr` (a Haar measure), identifies the diagonal factor
with the block sum (`realTwoBlockEntries`) and the upper rectangle with `packedTail` by its four
blocks, and transports the product measure and the density along the size identification.

The complex module uses the explicit complex Haar density and the density `|det g₂|_ℂ^{-k}`; here the
general linear Haar measures are arbitrary and the density is `|det g₂|^{-k}`.
[Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
