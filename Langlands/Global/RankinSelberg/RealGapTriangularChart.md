# Real Haar integration in the triangular split chart

This module is the real counterpart of the Library's `ComplexGapTriangularChart`.

The outer variables `Outer k q = ((GL_k(ℝ) × ℝ^{q+1}) × O(k + q + 1)) × ℝ^k` are the leading matrix `g₁`,
the logarithmic tail diagonal `y`, the orthogonal factor `u` and the first rectangular column `x`.

* `retainedMatrix (((g₁, y), u), x) = u · diag(1, torus y) · packedTail (firstRectangle x) 1`, where
  `RealIwasawa.torus y` is the diagonal matrix with entries `exp(y_i)`.
* `triangularRightChart (p, (X, Z)) = retainedMatrix p · packedTail (laterRectangle X) Z · diag(g₁, 1)`
  for a `k × q` rectangle `X` and `Z ∈ N_{q+1}(ℝ)`.
* `continuous_packedTail`, `continuous_retainedMatrix` and `continuous_triangularRightChart` give
  continuity of these maps.
* `diagonalWeightMeasure k q` is the tail diagonal measure `RealGapTailIwasawa.tailDiagonalMeasure q`
  (Lebesgue measure with the root modulus) with the additional density `|det torus y|^{-k}`.
* `outerMeasure k q μ η₁ κ = ((η₁ × diagonalWeightMeasure) × κ) × rowMeasure μ k`.

`RealGapTriangularChartStatement` (proved by `realGapTriangularChart`): for `0 < k`, an additive
Haar measure `μ` on `ℝ`, Haar measures `η` on `GL_{k+q+1}(ℝ)` and `η₁` on `GL_k(ℝ)`, and a Haar
measure `κ` on `O(k + q + 1)` invariant under inversion, there is `c > 0` with

`η = c • map triangularRightChart (outerMeasure μ η₁ κ × (rectangularMeasure μ k q × entryHaar μ (q + 1)))`.

The proof starts from `realGapRightChart` with a Haar measure on `GL_{q+1}(ℝ)` (Mathlib's
`Measure.haar`) and inserts the tail Iwasawa formula `realGapTailIwasawa` for that measure, with the
normalized Haar probability measure on `O(q + 1)`. The determinant weight `|det g₂|^{-k}` depends only
on the diagonal factor, because orthogonal matrices have `|det| = 1` and unipotent matrices
determinant `1`, so it moves onto the tail diagonal. Right invariance of `κ` absorbs the embedded
orthogonal tail factor `diag(1, u₂)`. The rectangle shear `realGapRectangleShear` then separates the
first column from the later columns, and the block identities of `RealGapUpperTail` identify the
composite chart with `triangularRightChart`.

The complex module uses the explicit complex Haar densities; here `η` and `η₁` are arbitrary Haar
measures and the constant `c` absorbs the normalizations.
[Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, pp. 72–73](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
