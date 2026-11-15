# Integrability of the block chart bound for `P_{a,k}` of `GL_{a+k}(ℂ)`

Lean module: `Langlands.Representation.Archimedean.ComplexBlockChartIntegralStatement`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It states one proposition and proves nothing. The
proposition is the analytic input for the Langlands lemma along the maximal parabolic subgroup
`P_{a,k}` of `GL_{a+k}(ℂ)` when the last `k` exponents are tied (equal real parts); see "Use" below.

## Definitions

All in the namespace `Langlands.Archimedean.ComplexBlockChart`; `X ∈ M_{k×a}(ℂ)` is a complex
`k × a` matrix and `Xᴴ` its conjugate transpose.

* `colsUpTo X l` (for `l < a`): the `k × (l+1)` matrix `X_{≤l}` of the columns `0, …, l` of `X`.
* `rowsFrom X j` (for `j < k`): the `(k−j) × a` matrix `X^{(j)}` of the rows `j, …, k−1` of `X`.
* `colGram X l = Re det(1 + X_{≤l}ᴴ X_{≤l})` and `rowGram X j = Re det(1 + X^{(j)} X^{(j)ᴴ})`.
  The matrices are positive definite Hermitian, so the determinants are positive real numbers
  (and taking real parts loses nothing); this is not needed for the statement to make sense.
* `blockChartBound ε X = ∏_{l<a} colGram X l ^ ε_l · ∏_{j<k} (1 if j = 0, else (rowGram X j)⁻¹)`,
  with real powers `^` (`Real.rpow`).

## The statement

`ComplexBlockChartIntegrableStatement`: for all `a, k ∈ ℕ` and `ε : Fin a → ℝ` with

`∑_{l ≥ j} (ε_l + 1) < 0` for every `j < a`

(written `∑_l (if j ≤ l then ε_l + 1 else 0) < 0`), the function
`X ↦ blockChartBound ε X` is integrable on `Fin k → Fin a → ℂ` (Lebesgue measure, the product of
the Lebesgue measures of `ℂ`), with `X` read as a matrix (`Matrix.of`).

For `k = 1` this is the integrability of `x ↦ ∏_l (1 + ∑_{i ≤ l} |x_i|²)^{ε_l}` on `ℂ^a`
(module `ComplexPartialSqIntegral`).

## Provenance

Derived, internal; no literature source is claimed. It is the convergence of the Jacquet integral
over `N̄_{P_{a,k}}` of the spherical bound of a principal series whose last `k` exponents are tied:
for `n̄(X) = [[1, 0], [X, 1]]`, the Gram determinant of the rows `≥ l` of `n̄(X)` is
`colGram X (l−1)` for `1 ≤ l ≤ a` and `rowGram X (l−a)` for `a ≤ l < a+k` (Schur complements), and
the chart bound of a principal-series function has exponent `−1` at every tied position. This is a
special case of the Gindikin–Karpelevich convergence criterion for intertwining integrals.

Intended proof (for the proof task): induction on `k`. Integrate row `0` of `X`, `x ∈ ℂ^a`. With
`X'` the remaining rows and `Q = 1 + X'ᴴX'`, the matrix determinant lemma gives
`colGram X l = colGram X' l · (1 + x_{≤l} Q_{≤l}^{-1} x_{≤l}ᴴ)`. With the LDL decomposition
`Q = L D Lᴴ` (Mathlib `LDL.lower_conj_diag`) and `z_i = (x (Lᴴ)^{-1})_i / √d_i`, the inner integral
is `det Q · ∫_{ℂ^a} ∏_l (1 + ∑_{i≤l}|z_i|²)^{ε_l} dz`, finite by `ComplexPartialSqIntegral`. Since
`det Q = rowGram X 1` (Weinstein–Aronszajn, `Matrix.det_one_add_mul_comm`) and
`rowGram X (j+1) = rowGram X' j`, the remaining integrand is `C · blockChartBound ε X'`.

## Use

In Task 7063, ties of the Langlands order are handled by the Langlands lemma along `P_{a,k}` with
the last block of `k` tied exponents: this statement gives the convergence of the partial Jacquet
integral over `N̄_{P_{a,k}}` and the dominating function for its limit argument.
