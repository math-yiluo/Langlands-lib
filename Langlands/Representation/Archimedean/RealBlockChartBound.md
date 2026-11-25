# Growth of real principal-series functions along the opposite unipotent radical of `P_{a,k}`

Lean module: `Langlands.Representation.Archimedean.RealBlockChartBound`.

This module was written for the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
generalizes the chart bound of `ParabolicChartBound` (one row, `P_{m,1}`) to the opposite
unipotent radical `n̄(X) = [[1, 0], [X, 1]]` of the maximal parabolic subgroup `P_{a,k+1}` of
`GL_{a+k+1}(ℝ)`, for a principal series whose last `k+1` exponents are tied. The resulting bound
is the function `RealBlockChart.blockChartBound` of the statement module
`RealBlockChartIntegralStatement`. The module is the real analogue of
`ComplexBlockChartBound` and follows its structure.

Notation: `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`, `O(N)` is `unitaryCompact ℝ N`;
`Iwasawa.diagonalUnits z = diag(z)` and `upperUnipotent` are the Library's. `gram l y`
(`GramFormula`, module `PrincipalSeriesGramFormula`) is the determinant of the padded Gram
matrix `paddedGram l y` of the rows `≥ l` of `y` (the entries `(y yᵀ)_{pq}` for `p, q ≥ l`, the
identity elsewhere). `blockLower`, `blockLowerGL` and `finSumFinEquiv` (identifying `Fin (a+k)`
with `Fin a ⊕ Fin k`) come from `RealBlockParabolicIntegrationStatement`; `colGram`, `rowGram`,
`blockChartBound` from `RealBlockChartIntegralStatement`; `gram_mul_orthogonal`,
`gram_diagonal_mul` and `sum_mul_eq_sum_sub` from `ParabolicChartBound`; `gram_pos`,
`mul_transpose_eq_one_of_mem` and `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`
(Iwasawa decomposition) from `PrincipalSeriesGramFormula`. Declarations without a prefix are in
the namespace `Langlands.Archimedean.RealBlockChart`.

## The statement

`RealBlockChartBoundStatement`: let `a, k ∈ ℕ`, `F : GL_{a+k+1}(ℝ) → ℂ`, `c : (ℝˣ)^{a+k+1} → ℂ`
and `σ : ℕ → ℝ` satisfy `F(diag(z) u g) = c(z) F(g)` for all `z`, upper unipotent `u` and `g`,
and `‖c(z)‖ = ∏_l |z_l|^{σ_l}`; let `C ∈ ℝ` with `‖F(κ)‖ ≤ C` for `κ ∈ O(a+k+1)`; and let
`(σ_{a+j} − σ_{a+j−1})/2 = −1/2` for `1 ≤ j ≤ k`. Then for all `X ∈ M_{(k+1)×a}(ℝ)` and
`κ ∈ O(a+k+1)`,

`‖F(n̄(X) κ)‖ ≤ C · blockChartBound ε X`, `ε_l = (σ_{l+1} − σ_l)/2`,

i.e. `≤ C ∏_{l<a} det(1 + X_{≤l}ᵀ X_{≤l})^{ε_l} ∏_{1≤j≤k} det(1 + X^{(j)} X^{(j)ᵀ})^{−1/2}`
(real powers), where `X_{≤l}` are the columns `0, …, l` and `X^{(j)}` the rows `j, …, k` of `X`.
Proved as `Langlands.Archimedean.realBlockChartBound`.

The block size is written `k+1` so that the row `0` of `X` exists; `n̄(X)` lies in
`GL_{a+(k+1)}(ℝ)`. For `k = 0` the tie hypothesis is vacuous and the bound is the one-row bound
`∏_{l<a} (1 + ∑_{i≤l} x_i²)^{ε_l}`.

For a principal series of signed-power characters `χ_l(x) = sgn(x)^{p_l} |x|^{s_l}` of
`GL_N(ℝ)` (normalized induction), `σ_l = Re s_l + (N−1)/2 − l` (module `PartialJacquetIntegral`,
`norm_principalSeriesCharacter`), so `(σ_{l} − σ_{l−1})/2 = (Re s_l − Re s_{l−1} − 1)/2` and the
tie hypothesis says `Re s_{a+j} = Re s_{a+j−1}` for `1 ≤ j ≤ k`: the last `k+1` exponents have
equal real parts.

Provenance. Derived, internal infrastructure without a literature source: the estimate of a
principal-series function by the spherical function of its absolute character, evaluated on
`N̄_P` through Gram determinants (Schur complements).

## The general growth bound

* `prod_tail_sq_eq_gram`: if `y κ = diag(z) u k` (Iwasawa, `κ, k ∈ O(N+1)`), then
  `gram l y = (∏_{j≥l} z_j)²`. Right multiplication by an orthogonal matrix does not change the
  padded Gram matrix (`gram_mul_orthogonal`), and `gram_diagonal_mul` computes it for
  `diag(z) u k`.
* `norm_le_gram`: for every `y` with `gram 0 y = 1` (i.e. `det(y)² = 1`) and `κ ∈ O(N+1)`,
  `‖F(y κ)‖ ≤ C ∏_{l<N} gram (l+1) y ^ ((σ_{l+1} − σ_l)/2)`. Proof as in
  `ParabolicChartBound.norm_le_chart`: with the Iwasawa decomposition `y κ = diag(z) u k`,
  `‖F(y κ)‖ = ‖c(z)‖ ‖F(k)‖ ≤ ‖c(z)‖ C`, and
  `∑_l σ_l log|z_l| = ∑_{l<N} (σ_{l+1} − σ_l) T_{l+1}` with
  `T_l = ∑_{j≥l} log|z_j| = log(gram l y)/2` (summation by parts, `sum_mul_eq_sum_sub`; `T_0 = 0`
  by the hypothesis on `y`).

## Gram determinants of `n̄(X)`

With `Z = n̄(X) = blockLower X` for `X ∈ M_{k×a}(ℝ)`:

* `blockLower_mul_transpose`: `Z Zᵀ = [[1, Xᵀ], [X, X Xᵀ + 1]]` (reindexed by `finSumFinEquiv`).
* `gram_blockLower_le`: for `l ≤ a`, `gram l Z = det(1 + X_{<l} X_{<l}ᵀ)` (`colsBelow X`: the
  columns `< l`). The padded Gram matrix is `[[1, Mᵀ], [M, X Xᵀ + 1]]` with `M = maskCols l X` (the
  columns `< l` of `X` replaced by `0`) (`paddedGram_blockLower_le`; the auxiliary
  `one_apply_castAdd_natAdd` and `one_apply_natAdd_castAdd` say the identity has no entries across
  the two blocks), whose determinant is `det(X Xᵀ + 1 − M Mᵀ)` (`Matrix.det_fromBlocks_one₁₁`), and
  `X Xᵀ + 1 − M Mᵀ = 1 + X_{<l} X_{<l}ᵀ` (`sub_maskCols`, with `sum_castLE`).
* `gram_blockLower_ge`: for `j ≤ k`, `gram (a+j) Z = det(1 + X^{≥j} X^{≥j ᵀ})` (`rowsGe X`: the
  rows `≥ j`, indexed through `fromIdx`). The padded Gram matrix is block diagonal
  `diag(1, padFrom j (X Xᵀ + 1))` (`paddedGram_blockLower_ge`), and `det (padFrom j M)` is the
  determinant of the principal submatrix of `M` on the indices `≥ j` (`det_padFrom`).

## The block chart bound

`blockLowerGL_val`: the matrix of `blockLowerGL X` is `blockLower X`. For
`X ∈ M_{(k+1)×a}(ℝ)` (block size `k+1`, so `a + (k+1)` is `(a+k) + 1`):
`gram (l+1) (n̄(X)) = colGram X l` for `l < a` (`gram_blockLower_col`, with the
Weinstein–Aronszajn identity `Matrix.det_one_add_mul_comm`),
`gram (a+j+1) (n̄(X)) = rowGram X (j+1)` for `j < k` (`gram_blockLower_row`) and
`gram 0 (n̄(X)) = 1` (`gram_blockLower_zero`). `norm_le_blockChartBound` applies `norm_le_gram`
with `N = a + k` and `y = n̄(X)`, splits the product over `Fin (a+k)` into the first `a` and the
last `k` factors (`Fin.prod_univ_add`), matches the first `a` factors with the first product of
`blockChartBound` and the last `k` with its second product (whose `j = 0` factor is `1`,
`Fin.prod_univ_succ`), and uses `(σ_{a+j+1} − σ_{a+j})/2 = −1/2` for the last `k` factors.
`realBlockChartBound` is `norm_le_blockChartBound` with the hypotheses reordered.
