# Extending `O(n)`-finite functions on `O(n)` to principal-series functions

Lean module: `Langlands.Representation.Archimedean.PrincipalSeriesExtension`.

A function of a real principal series of `GL_n(ℝ)` is determined by its restriction to `O(n)`
(Library: `eq_of_eqOn_unitaryCompact_of_mem_principalSeries`). This module proves the converse
for `O(n)`-finite functions. Every continuous, `O(n)`-finite function `φ` on `O(n)` with the sign
equivariance forced by the principal series is the restriction of an `O(n)`-finite function of
the smooth principal series. The statement is
`Langlands.Archimedean.PrincipalSeriesExtensionStatement`, proved as
`Langlands.Archimedean.principalSeriesExtension`. For characters of the shape
`χ_l(x) = χ_l(sgn x) |x|^(e_l)` the result is `PrincipalSeriesExtension.extension_mem_kFiniteFunctions`.
The extension is explicit (`PrincipalSeriesExtension.extension`) and linear in `φ`
(`extensionLinear`).

In the planned proof of the Langlands-quotient statement `RealStandardLanglandsQuotientStatement`
(Task 6749), this is used to pass between a principal series and its dual through their common
restriction to `O(n)`.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, `O(n)` is `Matrix.unitaryGroup (Fin n) ℝ`, and
`Unitary.toUnits : O(n) → GL_n(ℝ)` is the inclusion, with image `unitaryCompact ℝ n`.
`principalSeries ℝ n χ`, `principalSeriesCharacter`, `kFiniteFunctions` and
`Whittaker.rightTranslation` are the Library's. `gram`, `gramColumn`, `gramExpression`,
`complexify`, `signReal`, `signUnit`, `shiftedExponent`, `realPositionExponent` and
`realPositionCharacter_eq_signUnit_mul` come from the Library module `PrincipalSeriesGramFormula`
(namespace `Langlands.Archimedean.GramFormula`). Declarations without a prefix are in the namespace
`Langlands.Archimedean.PrincipalSeriesExtension`.

## Definitions

* `signedOrthogonal x`: for a real `n × n` matrix `x`, the matrix with entries
  `gramColumn i j x · (√(gram i x))⁻¹ · (√(gram (i+1) x))⁻¹`. If `x = b κ` with `b` upper triangular
  with nonzero diagonal and `κ κᵀ = 1`, then `signedOrthogonal x = diag(signReal b_ii) · κ`
  (`signedOrthogonal_mul`). Hence it lies in `O(n)` for every `x ∈ GL_n(ℝ)` (`signedOrthogonal_mem`),
  and `signedOrthogonalPart x` is that element of `O(n)`.
* `signDiagonal d = diag(signReal d_0, …, signReal d_(n-1))` in `O(n)`, for `d : Fin n → ℝ`. The
  related `signMatrix a` is the same for `a : Fin n → ℝˣ`.
* `extension s φ x = gramExpression s 1 (complexify x) · φ(signedOrthogonalPart x)` for
  `s : Fin n → ℂ`, `φ : O(n) → ℂ` and `x ∈ GL_n(ℝ)`. The first factor is
  `∏_l G_l(x)^(s_l/2) G_{l+1}(x)^(-s_l/2)`, with `G_l = gram l x > 0` and principal complex powers.
* `extensionLinear s`: `φ ↦ extension s φ` as a `ℂ`-linear map.

## The statement

`PrincipalSeriesExtensionStatement`: let `n` be a natural number, `ds` a list of real blocks and
`φ : O(n) → ℂ` a function such that

* `φ` is continuous;
* the right translates `x ↦ φ(x k)`, `k ∈ O(n)`, span a finite-dimensional space;
* `φ(signDiagonal(a) · κ) = principalSeriesCharacter ℝ n (realPositionCharacter ds) (sgn a) · φ(κ)`
  for all `a ∈ (ℝˣ)ⁿ` and `κ ∈ O(n)`, where `sgn a = (signUnit a_i)_i`.

Then there is `f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n)`
with `f(κ) = φ(κ)` for every `κ ∈ O(n)`.

The third condition is necessary. `signDiagonal(a)` is the diagonal matrix of the signs `±1`. It
lies both in `O(n)` and in the diagonal torus, so every function of the principal series satisfies
the condition on `O(n)`. The statement applies to the standard modules `realStandardModule n ds`
only through their principal series: the Fourier conditions of induction blocks are not
addressed.

Provenance. Derived, internal infrastructure without a literature source. That restriction to `K`
identifies an induced representation with a space of functions on `K` is standard ("compact
picture" of the principal series). The content here is that the extension of an `O(n)`-finite
function is smooth. That is proved through the explicit Gram formula.

## Proof

1. **Values at `x = b κ`** (`extension_eq`). If `x = b κ` with `b` upper triangular with nonzero
   diagonal and `κ ∈ O(n)`, then
   `extension s φ x = ∏_l |b_ll|^(s_l) · φ(signDiagonal(b_ll) · κ)`. The first factor follows from
   `GramFormula.gramExpression_complexify_mul` with the polynomial `1`, and the second from
   `signedOrthogonal_mul`. In particular `extension s φ κ = φ(κ)` on `O(n)` (`extension_unitary`,
   `b = 1`).
2. **Equivariance** (`extension_mul_left`). Write `g = diag(a') u' k` (Library
   `exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact`). Then `diag(a) u g = B k` with
   `B = diag(a) u diag(a') u'` upper triangular and `B_ll = a_l a'_l`
   (`upperTriangular_mul_apply_self`). By step 1, `signDiagonal_mul` (from `signReal_mul`), the sign
   hypothesis on `φ`, `Complex.mul_cpow_ofReal_nonneg` and `GramFormula.principalSeriesCharacter_eq`,
   `extension (shiftedExponent n e) φ (diag(a) u g) = principalSeriesCharacter ℝ n χ a ·
   extension (shiftedExponent n e) φ g`.
3. **Smoothness** (`contMDiff_extension`). By the published `OrthogonalFinitePolynomial`,
   `φ(κ) = P(κ_ij)` on `O(n)` for a polynomial `P`. By step 1 and
   `GramFormula.gramExpression_complexify_mul`,
   `extension s φ x = gramExpression s P (complexify x)` for all `x` (`extension_eq_gramExpression`).
   This function is `C^∞` on the invertible real matrices (`contDiffOn_gramExpression`).
   Determinants, padded Gram matrices and `gramColumn` are polynomial in the entries
   (`contDiff_det_comp`, `contDiff_gram`, `contDiff_gramColumn`). Near an invertible matrix every
   `gram l` is positive (`GramFormula.gram_pos`), so `(G_l)^c = exp(log(G_l) · c)` there and is
   smooth (`contDiffAt_ofReal_cpow`). Evaluation of `P` preserves smoothness
   (`contDiffAt_mvPolynomial_eval`). The Library's `contMDiff_of_contDiffOn` transfers smoothness to
   `GL_n(ℝ)`. Together with step 2 this gives `extension_mem_principalSeries`.
4. **`O(n)`-finiteness** (`extension_mem_kFiniteFunctions`). For `k ∈ O(n)`, the right translate by
   `k` of `extension s φ` is `extension s (κ ↦ φ(κ k))` (`rightTranslation_extension`). Both lie in the
   principal series (Library `rightTranslation_mem_principalSeries`; step 3 for the translate of `φ`,
   whose own translates span a subspace of those of `φ`, `finiteDimensional_translate`). Both agree
   on `O(n)` by step 1, so they are equal by the Library's
   `eq_of_eqOn_unitaryCompact_of_mem_principalSeries`. Hence the span of the translates of
   `extension s φ` lies in the image under `extensionLinear s` of the span of the translates of `φ`,
   which is finite-dimensional.
5. **Real blocks.** `principalSeriesExtension` applies step 4 with
   `e = GramFormula.realPositionExponent ds` (`GramFormula.realPositionCharacter_eq_signUnit_mul`).
