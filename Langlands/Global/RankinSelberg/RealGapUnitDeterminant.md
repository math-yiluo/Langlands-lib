# The real triangular chart with retained determinant of absolute value one

This module is the real counterpart of the Library's `ComplexGapUnitDeterminant`.

* `normalizingScalar k q y = exp(-(∑_i y_i)/k)` as a unit of `ℝ`, and `leadingScalar k q y` the
  corresponding scalar matrix in `GL_k(ℝ)`.
* `unitRetained p = retainedMatrix p · diag(leadingScalar y, 1)` (`continuous_unitRetained`), and
  `unitDeterminantChart (p, (X, Z)) = unitRetained p · packedTail (laterRectangle X) Z · diag(g₁, 1)`
  (`continuous_unitDeterminantChart`).
* `normalizedAbs_unitRetained`: for `0 < k`, `|det (unitRetained p)| = 1`; the orthogonal factor has
  `|det| = 1`, the unipotent factor determinant `1`, the torus determinant `exp(∑ y_i)`, and the scalar
  contributes `exp(-∑ y_i)`.
* `normalizationWeight k q y = |det (leadingScalar y)|^q`, and `normalizationWeight_eq`: for `0 < k` it
  equals `exp(-q ∑_i y_i)` (`measurable_normalizationWeight`).
* `unitOuterMeasure k q μ η₁ κ` is `outerMeasure k q μ η₁ κ` with the density
  `normalizationWeight y`.

`RealGapUnitDeterminantStatement` (proved by `realGapUnitDeterminant`): for `0 < k`, an additive Haar
measure `μ` on `ℝ`, Haar measures `η` on `GL_{k+q+1}(ℝ)` and `η₁` on `GL_k(ℝ)`, and a Haar measure `κ`
on `O(k + q + 1)` invariant under inversion, there is `c > 0` with

`η = c • map unitDeterminantChart (unitOuterMeasure μ η₁ κ × (rectangularMeasure μ k q × entryHaar μ (q + 1)))`.

The proof starts from `realGapTriangularChart` and substitutes
`g₁ ↦ leadingScalar(y)^{-1} g₁`, `X ↦ normalizingScalar(y)^{-1} X`. Conjugation by the embedded scalar
rescales the later rectangle and fixes the unipotent tail (`packedTail_conj`), so the substitution
turns `triangularRightChart` into `unitDeterminantChart`. Left invariance of `η₁` absorbs the scalar in
the leading variable; the rectangular change of variables
(`Langlands.HarmonicAnalysis.haarMeasure_map_rectangular`) gives the Jacobian
`normalizationWeight y` of the rescaled `k × q` rectangle, and Tonelli's theorem moves it to the measure
on the logarithmic tail.

In the complex module the retained determinant has normalized absolute value one and the density is
`exp(-2q ∑ y_i)`, reflecting `|z|_ℂ = |z|²`; over `ℝ` the density is `exp(-q ∑ y_i)`.
[Jacquet, *Archimedean Rankin–Selberg integrals*, Section 10.2, determinant-one coordinates, pp. 73–74](https://www.math.columbia.edu/~hj/PerfectRankinSelberg.pdf).
