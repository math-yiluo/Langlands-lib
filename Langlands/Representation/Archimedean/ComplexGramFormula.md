# `U(n)`-finite complex principal-series functions as polarized Gram expressions

Lean module: `Langlands.Representation.Archimedean.ComplexGramFormula`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`). It is the
complex counterpart of the Library module `PrincipalSeriesGramFormula` (Worker 5220, for
`GL_n(ℝ)`), and reuses that module's ring-level lemmas.

The module gives a closed formula for every `U(n)`-finite function of a principal series of
`GL_n(ℂ)` on all of `GL_n(ℂ)`. The formula uses polynomials in the entries of `x` and of the
entrywise complex conjugate `conj x`, and complex powers of Gram determinants. It is written for
two independent complex matrices `Z` and `Y`, and the function is its value at `(x, conj x)`.
This polarization is the purpose of the module: along `t ↦ x exp(tH)` with `H` real diagonal both
`x exp(tH)` and `conj(x) exp(tH)` extend holomorphically in `t`, which the analyticity of
`U(n)`-finite matrix coefficients (`ComplexMatrixCoefficientAnalytic`) needs.

The general form, for characters of the shape `χ_l(z) = χ_l(z/|z|) (|z|²)^(e_l)`, is
`ComplexGramFormula.exists_gramExpression_eq`; for the Library's complex standard modules the
statement is `Langlands.Archimedean.ComplexPrincipalSeriesGramFormulaStatement`, proved as
`Langlands.Archimedean.complexPrincipalSeriesGramFormula`.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `unitaryCompact ℂ n` or
`Matrix.unitaryGroup (Fin n) ℂ`. `principalSeries ℂ n χ` is the Library's smooth principal
series: smooth `f` with `f(diag(a) u g) = principalSeriesCharacter ℂ n χ a · f(g)` for `u` upper
unipotent, where `principalSeriesCharacter ℂ n χ a = ∏ᵢ χᵢ(aᵢ) (|aᵢ|²)^((n-1)/2 - i)` (here
`‖a‖ ^ finrank ℝ ℂ = |a|²`). `kFiniteFunctions V K` is the subspace of `V` of functions whose
right translates by `K` span a finite-dimensional space. `complexStandardModule n ds` is
`principalSeries ℂ n (complexPositionCharacter ds)`. Rows and columns are numbered
`0, …, n-1`. `x̄` (Lean: `x.map (starRingEnd ℂ)`) is the entrywise conjugate. Declarations without
a prefix are in the namespace `Langlands.Archimedean.ComplexGramFormula`; `padded`,
`diagonalTail`, `columnFactor`, `gramColumnVector`, `shiftedExponent` and `ofReal_sq_cpow_half`
are from `Langlands.Archimedean.GramFormula` (Library).

## Definitions

Over any commutative ring `R`, for `x, y : Matrix (Fin n) (Fin n) R`:

* `paddedGram i x y`: the matrix equal to `x yᵀ` on the rows and columns `p, q ≥ i` and to the
  identity elsewhere.
* `gram i x y = det (paddedGram i x y)`: the polarized Gram determinant of the rows `i, …, n-1`.
  For `i ≥ n` it is `1`. It is symmetric: `gram i y x = gram i x y` (`gram_swap`, from
  `paddedGram_swap`).
* `gramColumn i j x y`: the determinant of `paddedGram i x y` with its `i`-th column replaced by
  `gramColumnVector i j x` (the `j`-th column of `x` on the rows `≥ i`, `0` elsewhere).

For complex matrices:

* `hatCoord i j Z Y = gramColumn i j Z Y · G_i^(-1/2) · G_{i+1}^(-1/2)` with `G_l = gram l Z Y`
  and Mathlib's principal complex powers.
* `gramExpression s P Z Y`, for `s : Fin n → ℂ` and
  `P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ`, is
  `(∏ₗ G_l^(s_l) · G_{l+1}^(-s_l)) · P(v)`, where `v (Sum.inl (i, j)) = hatCoord i j Z Y` and
  `v (Sum.inr (i, j)) = hatCoord i j Y Z`.
* `phaseUnit z = z / |z|` as a unit, for `z : ℂˣ`; `|phaseUnit z| = 1` (`norm_phaseUnit`).
* `complexPositionExponent ds l`: the exponent `t` of the `l`-th element of `ds` (a
  `ComplexCharacterData` `d` with `d.exponent = t`), and `0` past the end.

## The statement

`ComplexPrincipalSeriesGramFormulaStatement`: for every `n`, every list `ds` of complex
characters and every `f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)`,
there is a polynomial `P` in `2n²` variables such that for every `x ∈ GL_n(ℂ)`

`f(x) = gramExpression (shiftedExponent n (complexPositionExponent ds)) P x x̄`,

i.e. `f(x) = ∏ₗ G_l(x, x̄)^(s_l) G_{l+1}(x, x̄)^(-s_l) · P(κ̂(x, x̄), κ̂(x̄, x))` with
`s_l = t_l + (n-1)/2 - l`. Every `G_l(x, x̄)` is a positive real number (the squared norm of a
product of diagonal entries of the Iwasawa factor, see below), so at `(x, x̄)` the powers are
ordinary positive real powers.

Provenance. Derived, internal infrastructure with no literature source. Its content is the
standard fact that a vector of a principal series is determined by its restriction to `U(n)`
through the Iwasawa decomposition `x = b κ`, written explicitly: with `T_l = ∏_{m ≥ l} b_mm`, the
moduli `|b_ll|² = G_l/G_{l+1}` and the normalized unitary factor
`diag(b_ii/|b_ii|) κ = (κ̂_ij(x, x̄))` are read off from Gram determinants, and the restriction
to `U(n)` is polynomial in the entries and their conjugates (`UnitaryFinitePolynomial`). Used in
the proof of `ComplexStandardLanglandsQuotientStatement` (Task 7063) for the analyticity of
`U(n)`-finite matrix coefficients.

## Proof

**Ring level.** Let `b, c` be upper triangular and `κ νᵀ = 1`. Then
`(b κ)(c ν)ᵀ = b cᵀ` (`mul_mul_transpose`), and

* `paddedGram i (b κ) (c ν) = padded i b · (padded i c)ᵀ` (`paddedGram_mul`, row by row with
  `row_padded_of_le` and `row_padded_of_lt`), so
  `gram i (b κ) (c ν) = diagonalTail i b · diagonalTail i c` (`gram_mul`);
* the column-replaced matrix equals `padded i b · columnFactor i j c κ`
  (`updateCol_paddedGram_mul`), with `columnFactor` lower triangular, so
  `gramColumn i j (b κ) (c ν) = diagonalTail i b · (κ_ij · diagonalTail (i+1) c)`
  (`gramColumn_mul`).

These are the real module's computations with the second factor `c ν` in place of `b κ`.

**At `(x, x̄)`.** Let `b` be upper triangular with nonzero diagonal and `κ` unitary, so
`κ (κ̄)ᵀ = κ κ* = 1`. Since `conj(b κ) = b̄ κ̄`, with `b̄` upper triangular and
`diagonalTail i b̄ = conj (diagonalTail i b)`:

* `gram i (b κ) (conj(b κ)) = T_i conj(T_i) = |T_i|²` (`gram_mul_conj`), and the same for the
  swapped pair (`gram_conj_mul`);
* `hatCoord i j (b κ) (conj(b κ)) = (b_ii/|b_ii|) κ_ij` (`hatCoord_mul_conj`): the numerator is
  `T_i κ_ij conj(T_{i+1})`, the denominator `|T_i| |T_{i+1}|`, and `T_i = b_ii T_{i+1}`;
* `hatCoord i j (conj(b κ)) (b κ) = conj((b_ii/|b_ii|) κ_ij)` (`hatCoord_conj_mul`, the previous
  identity for `(b̄, κ̄)`);
* `gramExpression s P (b κ) (conj(b κ)) = ∏ₗ (|b_ll|²)^(s_l) · P(y, ȳ)` with
  `y = diag(b_ii/|b_ii|) κ` (`gramExpression_mul_conj`), using `|T_l| = |b_ll| |T_{l+1}|` and
  `((r q)²)^s (q²)^(-s) = (r²)^s` for `q > 0` (`ofReal_sq_mul_cpow_div`).

**Gram formula** (`exists_gramExpression_eq`). Assume `χ_l(z) = χ_l(z/|z|) (|z|²)^(e_l)`. Then
`principalSeriesCharacter ℂ n χ a = ∏ₗ (|a_l|²)^(s_l) · principalSeriesCharacter ℂ n χ (a/|a|)`
with `s = shiftedExponent n e` (`principalSeriesCharacter_eq`; the half-modulus factor is `1` at
the phases). Let `f` be `U(n)`-finite in the principal series of `χ`. By
`UnitaryFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors` (with `g = 1`) there is `P`
with `f(k) = P(k, k̄)` on `U(n)`. Write `x = diag(a) u k` (the Library's Iwasawa decomposition
`ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary`) and `b = diag(a) u`, so
`b_ll = a_l`. Then `y = diag(a/|a|) k` lies in `U(n)` (`diagonalUnits_phaseUnit_mem`),
`f(y) = principalSeriesCharacter ℂ n χ (a/|a|) · f(k)`, and

`gramExpression s P x x̄ = ∏ₗ (|a_l|²)^(s_l) · f(y) = principalSeriesCharacter ℂ n χ a · f(k) = f(x)`.

**Standard modules.** `complexPositionCharacter_eq_phaseUnit_mul` checks the hypothesis for the
position characters of `ds`: for `d.character z = (z/|z|)^m |z|^(2t)` one has
`d.character(z/|z|) = (z/|z|)^m` and `|z|^(2t) = (|z|²)^t` (`ofReal_cpow_two_mul`); past the end
both sides are `1`. `complexPrincipalSeriesGramFormula` is then `exists_gramExpression_eq`.
