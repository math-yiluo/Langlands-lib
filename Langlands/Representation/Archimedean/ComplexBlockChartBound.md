# Growth of complex principal-series functions along the opposite unipotent radical of `P_{a,k}`

Lean module: `Langlands.Representation.Archimedean.ComplexBlockChartBound`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It generalizes the chart bound of
`ComplexParabolicChartBound` (one row, `P_{m,1}`) to the opposite unipotent radical
`n̄(X) = [[1, 0], [X, 1]]` of the maximal parabolic subgroup `P_{a,k+1}` of `GL_{a+k+1}(ℂ)`, for a
principal series whose last `k+1` exponents are tied. The resulting bound is the function
`ComplexBlockChart.blockChartBound` of the statement module `ComplexBlockChartIntegralStatement`.

Notation: `GL_N(ℂ)` is `Langlands.GeneralLinear N ℂ`, `U(N)` is `unitaryCompact ℂ N`;
`Iwasawa.diagonalUnits z = diag(z)` and `upperUnipotent` are the Library's. `gram l y z`
(`ComplexGramFormula`) is the determinant of the padded Gram matrix of the rows `≥ l` of `y` and
`z` (the entries `(y zᵀ)_{pq}` for `p, q ≥ l`, the identity elsewhere), and `paddedGram` the padded
matrix. `blockLower`, `blockLowerGL`, `finSumFinEquiv` (identifying `Fin (a+k)` with
`Fin a ⊕ Fin k`) come from `ComplexBlockParabolicIntegrationStatement`; `colGram`, `rowGram`,
`blockChartBound` from `ComplexBlockChartIntegralStatement`; `paddedGram_mul_unitary` and
`sum_mul_eq_sum_sub` from `ComplexParabolicChartBound`. Declarations without a prefix are in the
namespace `Langlands.Archimedean.ComplexBlockChart`.

## The statement

`ComplexBlockChartBoundStatement`: let `F : GL_{a+k+1}(ℂ) → ℂ`, `c : (Fin (a+k+1) → ℂˣ) → ℂ` and
`σ : ℕ → ℝ` satisfy `F(diag(z) u g) = c(z) F(g)` for all `z`, upper unipotent `u` and `g`, and
`‖c(z)‖ = ∏_l |z_l|^{σ_l}`; let `‖F(κ)‖ ≤ C` for `κ ∈ U(a+k+1)`; and let
`(σ_{a+j} − σ_{a+j−1})/2 = −1` for `1 ≤ j ≤ k`. Then for all `X ∈ M_{(k+1)×a}(ℂ)` and
`κ ∈ U(a+k+1)`,

`‖F(n̄(X) κ)‖ ≤ C · blockChartBound ε X`, `ε_l = (σ_{l+1} − σ_l)/2`,

i.e. `≤ C ∏_{l<a} (Re det(1 + X_{≤l}ᴴ X_{≤l}))^{ε_l} ∏_{1≤j≤k} (Re det(1 + X^{(j)} X^{(j)ᴴ}))^{−1}`.
Proved as `Langlands.Archimedean.complexBlockChartBound`.

For a principal series of phase-power characters `χ_l(z) = χ_l(z/|z|)(|z|²)^{e_l}`,
`σ_l = 2(Re e_l + (N−1)/2 − l)`, so the condition says `Re e_{a+j} = Re e_{a+j−1}`: the last
`k+1` exponents have equal real parts.

Provenance. Derived, internal infrastructure without a literature source: the estimate of a
principal-series function by the spherical function of its absolute character, evaluated on
`N̄_P` through Gram determinants (Schur complements).

## The general growth bound

* `prod_tail_sq_eq_gram`: if `y κ = diag(z) u k` (Iwasawa, `κ, k` unitary), then
  `gram l y ȳ = |∏_{j≥l} z_j|²`. Right multiplication by a unitary matrix does not change the
  polarized padded Gram matrix (`paddedGram_mul_unitary`), and
  `ComplexGramFormula.gram_mul_conj` computes it for `diag(z) u k`.
* `gramRe y l = Re gram l y ȳ`; it is positive for invertible `y` (`gramRe_pos`).
* `norm_le_gram`: for every `y` with `gramRe y 0 = 1` (i.e. `|det y| = 1`) and `κ ∈ U(N+1)`,
  `‖F(y κ)‖ ≤ C ∏_{l<N} gramRe y (l+1)^{(σ_{l+1} − σ_l)/2}`. Proof as in
  `ComplexParabolicChartBound.norm_le_chart`: `‖F(y κ)‖ = ‖c(z)‖ ‖F(k)‖`, and
  `∑_l σ_l log|z_l| = ∑_{l<N} (σ_{l+1} − σ_l) T_{l+1}` with `T_l = ∑_{j≥l} log|z_j| = log(gramRe y l)/2`
  (summation by parts, `T_0 = 0`).

## Gram determinants of `n̄(X)`

With `Z = n̄(X)` for `X ∈ M_{k×a}(ℂ)`:

* `blockLower_mul_conjTranspose`: `Z Zᴴ = [[1, Xᴴ], [X, X Xᴴ + 1]]` (reindexed).
* `gram_blockLower_le`: for `l ≤ a`, `gram l Z Z̄ = det(1 + X_{<l} X_{<l}ᴴ)` (`colsBelow X`: the
  columns `< l`). The padded Gram matrix is `[[1, Mᴴ], [M, X Xᴴ + 1]]` with `M = maskCols l X` (the
  columns `< l` of `X` replaced by `0`) (`paddedGram_blockLower_le`), whose determinant is
  `det(X Xᴴ + 1 − M Mᴴ)` (`Matrix.det_fromBlocks_one₁₁`), and `X Xᴴ − M Mᴴ = X_{<l} X_{<l}ᴴ`
  (`sub_maskCols`, with `sum_castLE`).
* `gram_blockLower_ge`: for `j ≤ k`, `gram (a+j) Z Z̄ = det(1 + X^{(j)} X^{(j)ᴴ})` (`rowsGe X`: the
  rows `≥ j`). The padded Gram matrix is block diagonal `diag(1, padFrom j (X Xᴴ + 1))`
  (`paddedGram_blockLower_ge`), and `det (padFrom j M)` is the determinant of the principal
  submatrix of `M` on the indices `≥ j` (`det_padFrom`).

## The block chart bound

For `X ∈ M_{(k+1)×a}(ℂ)` (block size `k+1`, so `a + (k+1) = (a+k) + 1`):
`gramRe (n̄(X)) (l+1) = colGram X l` for `l < a` (`gramRe_blockLower_col`, with the
Weinstein–Aronszajn identity `Matrix.det_one_add_mul_comm`), `gramRe (n̄(X)) (a+j+1) =
rowGram X (j+1)` (`gramRe_blockLower_row`) and `gramRe (n̄(X)) 0 = 1` (`gramRe_blockLower_zero`).
`norm_le_blockChartBound` applies `norm_le_gram` with `y = n̄(X)`, splits the product over
`Fin (a+k)` into the first `a` and the last `k` factors (`Fin.prod_univ_add`), and uses
`(σ_{a+j+1} − σ_{a+j})/2 = −1` and `x^{−1} = x⁻¹` for the last `k` factors.
