# Joint ordinary-tail domination in the real gap recurrence

This module is the real counterpart of the Library's `ComplexGapOrdinaryTailBound`. Real matrices carry
the operator (row-sum) norm `Matrix.Norms.Operator`, as in `RealGapLeadingSchwartz`, whose `matrixDecay`
appears in the statement.

* `entrySup X` is the entrywise supremum norm of a real matrix (the norm of the underlying function),
  with `entrySup_nonneg`, `norm_entry_le_entrySup`, `entrySup_le_opNorm` and
  `opNorm_le_entrySup : ‖X‖ ≤ n · entrySup X` for matrices with `n` columns. The block estimates
  `RealTwoBlockHaar.rightTail_norm_bounds` are stated for the entrywise norm and are converted with these.
* `exists_ordinaryTail_exponential_bound`: for `0 < k < r + 1`, `0 ≤ B`, `A + 1 ≤ T`, there are `J`, `p`, `q`
  with, for `g = rightTail h X v`, `z = alpha h^{-1}` and `x = blockLog y z`,
  `exp(A ∑|y_i| + B ∑|z_i| + T ∑ y_i − J rootPos x) ≤ exp(−∑|y_i|) · (n²(1 + ‖tailColumns g‖))^p ·
  (n (1 + ‖row_{last}(g^{-1})‖))^q`, `n = r + 1`. The negative parts of `z` are bounded by the logarithm of
  `n²(1 + ‖tailColumns g‖)` (the inverse diagonal entries of the Iwasawa factor of `h^{-1}` are entries of
  an orthogonal matrix times `h`), and the positive part of the last coordinate of `x` by the logarithm of
  `n(1 + ‖row_{last}(g^{-1})‖)`, via `realTwoBlockIwasawa`; then `RealGapTorusBound.exponent_le` applies.

`RealGapOrdinaryTailBoundStatement` (proved by `realGapOrdinaryTailBound`): for `0 < k < r + 1`, `0 ≤ B`,
`A + 1 ≤ T`, Schwartz functions `Φ` on `(r + 1) × (r + 1 − k)` matrices and `Ψ` on `ℝ^{r+1}`, and `m`, `p`,
`q : ℕ`, there are `J` and `C ≥ 0` with

`‖Φ(tailColumns g) Ψ(row_{last}(g^{-1}))‖ (1 + ‖tailColumns g‖)^m exp(A ∑|y_i| + B ∑|z_i| + T ∑ y_i − J rootPos x)
≤ C exp(−∑|y_i|) · matrixDecay p h · matrixDecay q X`

for all `y`, `h ∈ GL_{r+1−k}(ℝ)`, `X` and orthogonal `v`. Schwartz seminorms of sufficiently high order
absorb the polynomial costs, and `1 + ‖h‖`, `1 + ‖X‖` are at most `n²(1 + ‖tailColumns g‖)` (the complex
module has `n` here, for its entrywise norm).

This is an internal estimate supporting the absolute convergence of the larger-gap integrals in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
