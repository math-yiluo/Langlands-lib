# Change of variables through the twisted chart

Module `Langlands.BaseChange.TwistedLocalDescent.ChartChange`. Over an ultrametric, proper,
nontrivially normed field `𝕂`, with `σ` an isometric ring endomorphism and `dinv d = 1`:

- `twistedChart_zero`, continuity of the chart (`continuous_matrix_map`,
  `continuous_lowerInverse`, `continuous_twistedChart`).
- `map_restrict_closedBall_twistedChart`: let `A` be a continuous additive automorphism of `M_n`
  with `A X = twistedChartLinear B σ d dinv X`, `‖A⁻¹ Y‖ ≤ C ‖Y‖`, and `ν.map A = c • ν` for an
  additive Haar measure `ν`. If `0 < r ≤ 1` and `C · max(‖dinv‖‖d‖, 1) · r < 1`, then
  `(ν|_{B(0,r)}).map χ = c • ν|_{A(B(0,r))}` and `χ(B(0,r)) = A(B(0,r))` for the chart
  `χ = twistedChart B σ d dinv`. Here `A⁻¹(χ X) − X = A⁻¹(R(X))` with `R` the remainder, Lipschitz
  with constant `C · max(‖dinv‖‖d‖, 1) · r < 1` by `norm_twistedChartRemainder_sub_le`, and
  `OneBall` applies.
