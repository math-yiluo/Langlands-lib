# Extending `U(n)`-finite functions on `U(n)` to complex principal-series functions

Lean module: `Langlands.Representation.Archimedean.ComplexPrincipalSeriesExtension`.

Worker 140 wrote this module for Task 7063 (`f2d2e257-dd4b-4820-96ab-faa9c832ffb8`), the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of the Library module
`PrincipalSeriesExtension` (Worker 5220, for `GL_n(ℝ)`).

A function of a principal series of `GL_n(ℂ)` is determined by its restriction to `U(n)` (Library:
`ComplexDuality.eq_zero_of_mem_principalSeries_of_eqOn`). This module proves the converse for
`U(n)`-finite functions: every continuous, `U(n)`-finite function `φ` on `U(n)` with the phase
equivariance forced by the principal series is the restriction of a `U(n)`-finite function of the
smooth principal series. The statement is
`Langlands.Archimedean.ComplexPrincipalSeriesExtensionStatement`, proved as
`Langlands.Archimedean.complexPrincipalSeriesExtension`. For characters of the shape
`χ_l(z) = χ_l(z/|z|) (|z|²)^(e_l)` the result is
`ComplexPrincipalSeriesExtension.extension_mem_kFiniteFunctions`. The extension is explicit
(`ComplexPrincipalSeriesExtension.extension`) and linear in `φ` (`extensionLinear`). In the proof of
`ComplexStandardLanglandsQuotientStatement` it shows that the partial Jacquet integral of a
`U(n)`-finite principal-series function is again a smooth `U(n-1)`-finite principal-series function.

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is `Matrix.unitaryGroup (Fin n) ℂ`, and
`Unitary.toUnits : U(n) → GL_n(ℂ)` is the inclusion, with image `unitaryCompact ℂ n`.
`principalSeries ℂ n χ`, `principalSeriesCharacter`, `kFiniteFunctions`, `complexStandardModule` and
`Whittaker.rightTranslation` are the Library's. `gram`, `hatCoord`, `gramExpression`, `phaseUnit`,
`complexPositionExponent`, `gramExpression_mul_conj`, `principalSeriesCharacter_eq` and
`complexPositionCharacter_eq_phaseUnit_mul` come from `ComplexGramFormula`,
`GramFormula.shiftedExponent` from `PrincipalSeriesGramFormula`, and `coordValue` from
`UnitaryFinitePolynomial`. `x̄` (Lean: `x.map (starRingEnd ℂ)`) is the entrywise conjugate.
Declarations without a prefix are in the namespace
`Langlands.Archimedean.ComplexPrincipalSeriesExtension`.

## Definitions

* `phaseMatrix a = diag(a₀/|a₀|, …, a_{n-1}/|a_{n-1}|)` in `U(n)`, for `a : Fin n → ℂˣ`. It is
  multiplicative in `a` (`phaseMatrix_mul`, from `phaseUnit_mul`) and `phaseMatrix 1 = 1`.
* `phaseOrth x`: the matrix with entries `hatCoord i j x x̄`. If `x = b κ` with `b` upper triangular
  with nonzero diagonal and `κ` unitary, then `phaseOrth x = diag(b_ii/|b_ii|) κ` (`phaseOrth_mul`),
  so for `x = diag(a) u k` (Iwasawa) it is `phaseMatrix a · k` (`phaseOrth_iwasawa`). Hence it lies in
  `U(n)` for every `x ∈ GL_n(ℂ)` (`phaseOrth_mem`), and `phaseOrthPart x` is that element of `U(n)`:
  the unitary Iwasawa factor of `x` for the triangular factor with positive diagonal.
* `extension s φ x = gramExpression s 1 x x̄ · φ(phaseOrthPart x)` for `s : Fin n → ℂ`,
  `φ : U(n) → ℂ` and `x ∈ GL_n(ℂ)`. The first factor is `∏_l G_l(x,x̄)^(s_l) G_{l+1}(x,x̄)^(-s_l)`.

## The statement

`ComplexPrincipalSeriesExtensionStatement`: for every `n`, every list `ds` of complex characters and
every continuous `φ : U(n) → ℂ` such that

* the right translates `x ↦ φ(x k)`, `k ∈ U(n)`, span a finite-dimensional space, and
* `φ(phaseMatrix a · κ) = principalSeriesCharacter ℂ n (complexPositionCharacter ds) (a/|a|) · φ(κ)`
  for all `a ∈ (ℂˣ)ⁿ` and `κ ∈ U(n)`,

there is `f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)` with
`f(κ) = φ(κ)` for every `κ ∈ U(n)`.

Provenance. Derived, internal infrastructure. That `K`-finite vectors of an induced representation
correspond to `K`-finite functions on `K` with the right `B ∩ K`-equivariance is the standard
compact picture of induced representations; the module gives the smooth extension explicitly. No
literature claim beyond this standard fact.

## Proof

1. **Values** (`extension_iwasawa`). For `x = diag(a) u k` with `u` upper unipotent and `k` unitary,
   `extension s φ x = ∏_l (|a_l|²)^(s_l) · φ(phaseMatrix a · k)`, by `gramExpression_mul_conj` with
   `P = 1` and `phaseOrthPart_iwasawa`. In particular `extension s φ k = φ(k)` on `U(n)`
   (`extension_unitary`).
2. **Equivariance** (`extension_mul_left`). Let `χ_l(z) = χ_l(z/|z|) (|z|²)^(e_l)` and let `φ` have
   the phase equivariance above. For `g = diag(a') u' k`, the product `diag(a) u diag(a') u'` is
   `diag(a a') u''` with `u''` upper unipotent (`exists_iwasawa_mul`). Step 1, multiplicativity of
   `phaseMatrix` and of `(|·|²)^s` on positive reals, and `principalSeriesCharacter_eq` give
   `extension(diag(a) u g) = principalSeriesCharacter ℂ n χ a · extension(g)`, with
   `s = shiftedExponent n e`.
3. **Smoothness** (`contDiffOn_gramExpression`, `extension_eq_gramExpression`,
   `contMDiff_extension`). By `UnitaryFinitePolynomial`, `φ = P(κ, κ̄)` on `U(n)` for a polynomial `P`.
   Then `extension s φ x = gramExpression s P x x̄` (both sides evaluated through step 1 and
   `gramExpression_mul_conj`). The right side is real-smooth on the invertible matrices: the entries
   of `x` and `x̄` are real-linear in `x`, polarized Gram and column determinants are polynomial in
   them, and at an invertible `x` every `gram l x x̄` is a positive real number
   (`gram_conj_eq_ofReal`, from the Iwasawa decomposition), so near `x` its complex powers are
   `exp(c · log)` of a smooth positive real function (`contDiffAt_ofReal_cpow`); `gram l x̄ x` equals
   `gram l x x̄` (`gram_swap`). The Library's `contMDiff_of_contDiffOn` transfers this to `GL_n(ℂ)`.
4. **Principal series and finiteness** (`extension_mem_principalSeries`,
   `rightTranslation_extension`, `extension_mem_kFiniteFunctions`). Steps 2 and 3 put the extension in
   the principal series. Right translation by `k ∈ U(n)` maps the extension of `φ` to the extension of
   `κ ↦ φ(κ k)`: both are in the principal series and agree on `U(n)` by step 1, hence are equal
   (`eq_of_eqOn_unitary`). So the span of the right translates of the extension lies in the image of
   the finite-dimensional span of the translates of `φ` under `extensionLinear`.

`complexPrincipalSeriesExtension` applies this with `e = complexPositionExponent ds` and
`complexPositionCharacter_eq_phaseUnit_mul ds`.

The entry, conjugate-entry and determinant smoothness lemmas are reused from
`ComplexStandardNontrivialProof`.
