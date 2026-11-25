# `O(n)`-finite principal-series functions as Gram-determinant expressions

Lean module: `Langlands.Representation.Archimedean.PrincipalSeriesGramFormula`.

This module gives an explicit closed formula for every `O(n)`-finite function of a real principal
series of `GL_n(ℝ)` on all of `GL_n(ℝ)`. The formula uses only polynomials in the matrix entries
and complex powers of Gram determinants. It is stated for the position characters of a list of
real blocks as `Langlands.Archimedean.PrincipalSeriesGramFormulaStatement`, and proved as
`Langlands.Archimedean.principalSeriesGramFormula`. A form for any characters of the shape
`χ_l(x) = χ_l(sgn x) |x|^(e_l)` is `GramFormula.exists_gramExpression_eq`.

The same expression makes sense for complex matrices. That is the purpose of the module: it lets
`t ↦ f(g exp(tH))` extend holomorphically in `t`, which the proof of the Langlands-quotient
statement `RealStandardLanglandsQuotientStatement` needs for the analyticity of
`O(n)`-finite matrix coefficients.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, `O(n)` is `unitaryCompact ℝ n` (as a
subgroup of `GL_n(ℝ)`) or `Matrix.unitaryGroup (Fin n) ℝ`. `principalSeries ℝ n χ` is the
Library's smooth principal series. Its elements are the `C^∞` functions `f` with
`f(diag(a) u g) = principalSeriesCharacter ℝ n χ a · f(g)` for `u` upper unipotent, where
`principalSeriesCharacter ℝ n χ a = ∏ᵢ χᵢ(aᵢ) |aᵢ|^((n-1)/2 - i)`. `kFiniteFunctions V K` is the
subspace of `V` of functions whose right translates by `K` span a finite-dimensional space.
Rows and columns are numbered `0, …, n-1`. Declarations without a prefix are in the namespace
`Langlands.Archimedean.GramFormula`.

## Definitions

Over any commutative ring `R`, for `x : Matrix (Fin n) (Fin n) R`:

* `paddedGram i x`: the matrix equal to the Gram matrix `x xᵀ` on the rows and columns `p, q ≥ i`
  and to the identity matrix elsewhere. Its rows and columns `≥ i` are the inner products
  `⟨x_p, x_q⟩` of the rows of `x` (bilinear, no conjugation).
* `gram i x = det (paddedGram i x)`: the Gram determinant `G_i(x)` of the rows `i, …, n-1` of `x`.
  For `i ≥ n` it is `det 1 = 1`.
* `gramColumnVector i j x`: the vector equal to the `j`-th column of `x` on the rows `≥ i` and to `0`
  on the rows `< i` (`i, j : Fin n`).
* `gramColumn i j x`: the determinant of `paddedGram i x` with its `i`-th column replaced by
  `gramColumnVector i j x` (`Matrix.updateCol`).

All three are polynomials in the entries of `x`, and they commute with ring homomorphisms applied
entrywise (`paddedGram_map`, `gram_map`, `gramColumn_map`).

For real and complex matrices:

* `complexify x = x.map Complex.ofRealHom`, a real matrix viewed as a complex matrix.
* `gramExpression s P Z`, for exponents `s : Fin n → ℂ`, a polynomial
  `P : MvPolynomial (Fin n × Fin n) ℂ` and a complex matrix `Z`, is

  `(∏ₗ G_l(Z)^(s_l/2) · G_{l+1}(Z)^(-(s_l/2))) · P(κ̂(Z))`, with
  `κ̂(Z)_ij = gramColumn i j Z · G_i(Z)^(-1/2) · G_{i+1}(Z)^(-1/2)`.

  Here `G_l = gram l`, `P(κ̂)` is `MvPolynomial.eval` at the family `(i, j) ↦ κ̂_ij`, and all powers
  are Mathlib's principal complex powers `Complex.cpow`.
* `signReal r` is `1` if `r > 0` and `-1` otherwise. `signUnit x` is the same sign as a unit of
  `ℝ`.
* `shiftedExponent n e l = e_l + ((n-1)/2 - l)` for `e : ℕ → ℂ` and `l : Fin n`.
* `realPositionExponent ds l` (for a list `ds` of real blocks) is the exponent of `|·|` in the
  character at position `l`: `t` for a block `.character d` with `d.exponent = t`; `t + |m|/2` and
  `t - |m|/2` at the two positions of a block `.induced d` with `d.exponent = t`,
  `d.weight = m`; `0` past the end. This matches the Library's `realPositionCharacter`,
  `realInducedFirstCharacter` and `realInducedSecondCharacter`.

## The statement

`PrincipalSeriesGramFormulaStatement`: for every `n`, every list `ds` of real blocks and every
`f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n)`, there
is a polynomial `P : MvPolynomial (Fin n × Fin n) ℂ` such that for every `x ∈ GL_n(ℝ)`

`f(x) = gramExpression (shiftedExponent n (realPositionExponent ds)) P (complexify x)`.

So `f(x) = ∏ₗ G_l(x)^(s_l/2) G_{l+1}(x)^(-s_l/2) · P(κ̂(x))` with
`s_l = realPositionExponent ds l + (n-1)/2 - l`. Every `G_l(x)` is a positive real number
(`gram_pos`), so the powers are the ordinary positive real powers. The statement applies to the
standard modules `realStandardModule n ds`, which lie inside this principal series. It says nothing
about the Fourier conditions that cut them out.

Provenance. This is derived, internal infrastructure with no literature source. Its content is the
standard fact that a vector of a principal series is determined by its restriction to `O(n)`
through the Iwasawa decomposition `x = b κ`, written explicitly. The diagonal part of `b` and the
`O(n)` part `κ` are read off from Gram determinants: `|b_ll| = (G_l/G_{l+1})^(1/2)` and
`κ̂(x) = diag(sgn b_ll) · κ`. The determinant `gramColumn` replaces the Gram–Schmidt formulas, so that
the expression is a polynomial in `x` and complex powers of polynomials in `x`. The restriction to
`O(n)` is a polynomial by `OrthogonalFinitePolynomial` (Library).

## Proof

1. **Triangular factorization** (section `Ring`). Let `b` be upper triangular
   (`Matrix.IsUpperTriangular`) and `κ κᵀ = 1`. Let `padded i b` be `b` on the rows and columns
   `≥ i`, padded by the identity, and let `diagonalTail i b = ∏_{l ≥ i} b_ll`. Since
   `(bκ)(bκ)ᵀ = b bᵀ` (`mul_mul_transpose`) and `b` is upper triangular, the rows `p ≥ i` of
   `padded i b` are the rows of `b`, and the rows `p < i` are rows of the identity. Comparing
   entries gives `paddedGram i (bκ) = padded i b · (padded i b)ᵀ` (`paddedGram_mul`). So
   `gram i (bκ) = diagonalTail i b ^ 2` (`gram_mul`), because `padded i b` is upper triangular with
   determinant `diagonalTail i b` (`det_padded`).
2. **Column replacement** (`updateCol_paddedGram_mul`). The matrix in `gramColumn i j (bκ)` equals
   `padded i b · columnFactor i j b κ`. Here `columnFactor` has entries `δ_lq` if `q < i` or `l < i`,
   `κ_lj` in column `q = i`, and `b_ql` otherwise. It is lower triangular
   (`columnFactor_isLowerTriangular`) with diagonal `1, …, 1, κ_ij, b_{i+1,i+1}, …`. So
   `gramColumn i j (bκ) = diagonalTail i b · κ_ij · diagonalTail (i+1) b` (`gramColumn_mul`).
3. **Complex powers** (`gramExpression_complexify_mul`). Let `d_l = b_ll ≠ 0`. By
   `diagonalTail_succ`, `diagonalTail l b = d_l · diagonalTail (l+1) b`. With
   `(r²)^(c/2) = |r|^c` for real `r ≠ 0` (`ofReal_sq_cpow_half`, via `cpow = exp(log · c)`) and
   `Complex.mul_cpow_ofReal_nonneg`, each factor `G_l^(s_l/2) G_{l+1}^(-s_l/2)` becomes `|d_l|^(s_l)`.
   Each `κ̂_ij` becomes `signReal(d_i) · κ_ij` (`mul_mul_inv_abs`). So
   `gramExpression s P (bκ) = ∏ₗ |d_l|^(s_l) · P(signReal(d_i) κ_ij)`.
4. **Principal series** (`exists_gramExpression_eq`). Let `f` be `O(n)`-finite in the principal
   series. By `OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors` (with `g = 1`)
   there is `P` with `f(k) = P(k_ij)` on `O(n)`. Write `x = diag(a) u k` by the Library's
   `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`, and take `b = diag(a) u` (upper
   triangular, `b_ll = a_l`). Then `f(x) = principalSeriesCharacter ℝ n χ a · f(k)`. The matrix
   `y = diag(sgn a) k` lies in `O(n)` (`diagonalUnits_signUnit_mem`). So `P(signReal(a_i) k_ij) = f(y)`,
   and `f(y) = principalSeriesCharacter ℝ n χ (sgn a) · f(k)`. Finally
   `principalSeriesCharacter ℝ n χ a = ∏ₗ |a_l|^(shiftedExponent n e l) ·
   principalSeriesCharacter ℝ n χ (sgn a)` (`principalSeriesCharacter_eq`). This uses the hypothesis
   `χ_l(x) = χ_l(signUnit x) |x|^(e_l)`, `|sgn| = 1` and `Complex.cpow_add`.
5. **Real blocks** (`realPositionCharacter_eq_signUnit_mul`). The position characters of real
   blocks satisfy that hypothesis with `e = realPositionExponent ds`: by `RealCharacterData.character_eq`
   for character blocks, and by the definitions of `realInducedFirstCharacter` and
   `realInducedSecondCharacter` for induction blocks, using `x/|x| = signReal x`.

`gram_pos` proves `0 < gram i x` for `x ∈ GL_n(ℝ)` from step 1 and the Iwasawa factorization.
