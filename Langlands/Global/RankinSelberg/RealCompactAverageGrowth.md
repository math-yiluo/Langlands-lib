# Polynomial sampling bounds for real normalized compact averages

Notation as in `RealNormalizedCompactAverage`: `d_ε` is the contracting diagonal with entries
`ε^i`, `averageScale c f₀ ε` the normalization and `inverseWeight f` the function `k ↦ f(k⁻¹)`.

## Auxiliary facts

* `contractionExponent n ds = Σ_i i · (Re μ_i + (n - 1)/2 - i)`, where `μ_i` are the position
  exponents of `ds` (`realPositionExponent`). `norm_contractionCharacter`: the inducing
  character on `d_ε` has norm `ε^(contractionExponent n ds)`, by the norm formula
  `norm_principalSeriesCharacter` for signed-power characters.
* `norm_averageScale`: `‖averageScale c f₀ ε‖ = (‖oppositeMass f₀‖ c)⁻¹ ·
  (ε⁻¹)^(D + contractionExponent n ds)`, with `D = contractionDegree n`.
* `height_unitary_mul_contractionDiagonal`: for `0 < ε ≤ 1` and orthogonal `k`, Jacquet's
  matrix height satisfies `realMatrixHeight (k d_ε) ≤ 2 n² ε^(-2n)`. The entries of an
  orthogonal matrix and of its inverse have absolute value at most one, and the entries of
  `d_ε` and `d_ε⁻¹` are at most `ε^(-n)`.

## Statement

`RealCompactAverageGrowthStatement`: for every `r`, `c > 0`, `ds`, `a`, every
`IsRealWhittakerIntertwiner r ds a B` and every standard vector `f₀`, there are `C ≥ 0` and
`M` such that for all `0 < ε ≤ 1`, every standard vector `f` and every `R` with
`‖f(k)‖ ≤ R` on `O(n)`,

`‖averageScale c f₀ ε · ∫_{O(n)} f(k⁻¹) (B f₀)(k d_ε) dk‖ ≤ C R ε^(-M)`.

`realCompactAverageGrowth` proves it: the moderate growth part of the intertwiner
hypothesis bounds `(B f₀)(g)` by `C₀ · realMatrixHeight(g)^N₀`; with the height bound this
gives `C₁ ε^(-2 n N₀)` on the compact translates of `d_ε`. The Haar measure of `O(n)` has
mass one, so the integral is at most `R C₁ ε^(-2 n N₀)`. The scale is at most a constant times
`ε^(-M₀)` for an integer `M₀` above `D + contractionExponent n ds`, since `ε⁻¹ ≥ 1`.

This is the real counterpart of the Library's `ComplexCompactAverageGrowth`; it gives the
sampling estimate of `RealWhittakerApproximateIdentity`.
