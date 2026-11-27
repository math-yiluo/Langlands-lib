# The twisted conjugation chart and its linear part

Module `Langlands.BaseChange.TwistedLocalDescent.ChartEstimate`. Let `𝕂` be a normed field,
`B` a block shape, `σ` a ring endomorphism of `𝕂`, and `d, dinv` matrices. For a matrix `X` write
`X_𝔲̄ = lowerPart B X` (strictly block lower part) and `X_𝔭 = upperPart B X = X − X_𝔲̄`.

- `lowerPart`, `upperPart` and their basic properties (`lowerPart_isLower`, `lowerPart_sub`,
  `upperPart_sub`, `norm_lowerPart_le`, `norm_upperPart_le`), `norm_mul_sub_mul_le`.
- `twistedChart B σ d dinv X = dinv (1 + X_𝔲̄)⁻¹ d (1 + X_𝔭) σ(1 + X_𝔲̄) − 1`, with
  `(1 + X_𝔲̄)⁻¹ = lowerInverse B X_𝔲̄`. When `dinv = d⁻¹` this is the matrix of
  `d⁻¹ ū⁻¹ d h σ(ū) − 1` for `ū = 1 + X_𝔲̄` and `h = 1 + X_𝔭`.
- `twistedChartLinear B σ d dinv X = X_𝔭 + σ(X_𝔲̄) − dinv X_𝔲̄ d`, its linear part, and
  `twistedChartRemainder` the difference.
- `twistedChartRemainder_eq` (for `dinv d = 1`): an explicit expression of the remainder as a sum
  of products each containing at least two factors among `X_𝔲̄`, `X_𝔭`, `σ(X_𝔲̄)`.
- `norm_lowerInverse_sub_le` and `norm_twistedChartRemainder_sub_le`: for `σ` isometric,
  `dinv d = 1`, `0 ≤ r ≤ 1` and `‖X‖, ‖Y‖ ≤ r` over an ultrametric field,
  `‖R(X) − R(Y)‖ ≤ max(‖dinv‖ ‖d‖, 1) · r · ‖X − Y‖`. Each term of the remainder is a product
  of factors of norm `≤ max(‖dinv‖‖d‖, 1)·r` or `≤ 1`, with at least two small factors; a
  difference of products is bounded factor by factor (`norm_mul_sub_mul_le`).
