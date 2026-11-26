# Exponential decay for the real weighted logarithmic tail Haar measure

This module is the real counterpart of the Library's `ComplexGapAlternateHaarDecay`; `δ(g) = |det g|`.

* `normalizedDet_torus`: `δ(torus y) = exp(∑_i y_i)`.
* `normalizedDet_retained`: `δ(retainedMatrix p) = exp(∑_i y_i)` for the tail logarithms `y` of `p`;
  the orthogonal factor has `|det| = 1` and the unipotent factor determinant `1`.
* `diagonalGrowth k q = k + 2 · #(strict upper entries of size q + 1)` (`diagonalGrowth_nonneg`), and
  `diagonalDecay k q y = exp(-(diagonalGrowth k q + 1) ∑_i |y_i|)`.

`RealGapAlternateHaarDecayStatement` (proved by `realGapAlternateHaarDecay`): for all `k`, `q`,
`diagonalDecay k q` is integrable for `diagonalWeightMeasure k q`, Lebesgue measure on `ℝ^{q+1}` with
the density `tailModulus y · |det torus y|^{-k}`.

The tail modulus is a product of factors `exp(-(y_j - y_i))` over the strict upper entries, each at most
`exp(2 ∑ |y|)`, and `|det torus y|^{-k} = exp(-k ∑ y_i) ≤ exp(k ∑ |y_i|)`, so the whole density is at most
`exp(diagonalGrowth k q · ∑ |y_i|)`. The integrand then is at most `exp(-∑ |y_i|)`, whose integral is
finite (`RealConvergenceAnalysis.lintegral_exp_neg_mul_sum_abs_lt_top`).

The complex module has the normalized determinant `exp(2 ∑ y_i)`, the squared root factors and the
coefficient `2k + 4 · #(entries)`; the real constants are halved accordingly.

This is an internal estimate supporting the absolute convergence of the larger-gap integrals in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
