# Gram expressions are `O(n)`-finite principal-series functions

Module `Langlands.Representation.Archimedean.RealGramFunction`. Helper module
of the proof that real standard modules are nonzero (`Langlands.Archimedean.realStandardNontrivial`,
module `Langlands.Representation.Archimedean.RealStandardNontrivialProof`), used in the proof of
`CuspidalArchimedeanStandardGenericStatement`.

The Library module `PrincipalSeriesGramFormula` shows that every `O(n)`-finite function of a real
principal series is a Gram expression. This module goes the other way. For every polynomial `P` in
the matrix entries that has the sign parity of the characters, `g ↦ gramExpression s P (g)` is a
smooth `O(n)`-finite function of the principal series, and its value at `1` is `P(1)`.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`. `gram`, `paddedGram`, `gramColumn`,
`gramColumnVector`, `gramExpression`, `complexify`, `signReal`, `signUnit` and `shiftedExponent`
come from the Library module `PrincipalSeriesGramFormula` (namespace
`Langlands.Archimedean.GramFormula`). `G_i(Z) = gram i Z` is the Gram determinant of the
rows `i, …, n-1` of `Z`. `principalSeries`, `principalSeriesCharacter`, `kFiniteFunctions`,
`kFiniteVectors`, `kFiniteSubalgebra`, `unitaryCompact` and `Whittaker.rightTranslation` are the
Library's. Declarations below are in the namespace `Langlands.Archimedean.RealGramFunction`.

## Definitions

* `gramEntry Z i j = gramColumn i j Z · G_i(Z)^(-1/2) · G_{i+1}(Z)^(-1/2)`, the normalized Gram
  column. For `Z = complexify(b κ)` with `b` upper triangular with nonzero diagonal and `κ ∈ O(n)`,
  it is `sgn(b_ii) κ_ij`.
* `gramFactor s Z = ∏_l G_l(Z)^(s_l/2) G_{l+1}(Z)^(-s_l/2)`. By `gramExpression_eq`,
  `gramExpression s P Z = gramFactor s Z · P((gramEntry Z i j)_{i,j})`. This holds by
  definition.
* `gramFunction s P : GL_n(ℝ) → ℂ`, `g ↦ gramExpression s P (complexify g)`.
* `orthogonalEval P : O(n) → ℂ`, `κ ↦ P(κ)`.
* `HasSignParity χ P`: for all `a ∈ (ℝˣ)ⁿ` and `Y`, multiplying row `i` of `Y` by
  `signReal a_i` multiplies `P(Y)` by `∏_l χ_l(signUnit a_l)`.

## Main theorems

```lean
theorem gramFunction_mem_kFiniteFunctions {χ : ℕ → ℝˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l)
    {P : MvPolynomial (Fin n × Fin n) ℂ} (hP : HasSignParity χ P) :
    gramFunction (shiftedExponent n e) P ∈
      kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)

theorem gramFunction_one (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    gramFunction s P 1 = MvPolynomial.eval (fun ij : Fin n × Fin n =>
      (((1 : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ)) P

theorem gramFunction_eq_extension (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    gramFunction s P = PrincipalSeriesExtension.extension s (orthogonalEval P)
```

Intermediate results: `gramFunction_mem_kFiniteVectors` (`O(n)`-finiteness for every `s` and
`P`), `contMDiff_gramFunction` (smoothness), and `gramFunction_mem_principalSeries`. The last one
is the principal-series law: it needs the hypotheses `hχ` and `hP` above.

## Proofs

* **Right translation by `O(n)`.** For `k kᵀ = 1`: the padded Gram matrices of `x k` and `x` are
  equal (`paddedGram_mul_orthogonal`), so the Gram determinants are equal
  (`gram_mul_orthogonal`). The Gram column vectors transform as
  `gramColumnVector i j (x k) = Σ_m k_mj · gramColumnVector i m x`, and the determinant is linear in
  a column (`det_updateCol_sum_smul`). Hence
  `gramColumn i j (x k) = Σ_m k_mj · gramColumn i m x` (`gramColumn_mul_orthogonal`). It follows
  that `gramEntry (x k) i j = Σ_m k_mj · gramEntry x i m` (`gramEntry_mul`) and
  `gramFactor s (x k) = gramFactor s x` (`gramFactor_mul`).
* **`O(n)`-finiteness.** Each function `g ↦ gramEntry g i j` has its right `O(n)`-translates in
  the span of the `n` functions `g ↦ gramEntry g i m` (`gramEntryFn_mem`). The factor
  `g ↦ gramFactor s g` is `O(n)`-invariant (`gramFactorFn_mem`). Both are elements of the Library
  subalgebra `kFiniteSubalgebra`, which is closed under products and polynomial evaluation
  (`eval_mem_subalgebra`, by induction on `P`). The Gram function is their product.
* **Smoothness and the principal-series law.** `gramFunction s P` is the Library extension
  `PrincipalSeriesExtension.extension s (orthogonalEval P)`
  (`PrincipalSeriesExtension.extension_eq_gramExpression`). Smoothness is
  `PrincipalSeriesExtension.contDiffOn_gramExpression`. The left `B`-equivariance is
  `PrincipalSeriesExtension.extension_mul_left`. Its hypothesis on sign diagonals is
  `orthogonalEval_signDiagonal_mul`, which follows from `HasSignParity` because
  `principalSeriesCharacter` at a sign vector is `∏_l χ_l(signUnit a_l)`
  (`principalSeriesCharacter_signUnit`).
* **Value at `1`.** `PrincipalSeriesExtension.extension_unitary` at `κ = 1`.

## Provenance

This is the converse of the Library's Gram formula (`PrincipalSeriesGramFormula`), and like it is
an explicit computation with the Iwasawa decomposition `g = b κ`. It was written in the project
for the nonvanishing proof. It does not follow a literature source and claims none.

## Lean checks

`lean_check` on the module alone and built with the other three nonvanishing modules: no errors or
warnings. Axioms: `propext`, `Classical.choice`, `Quot.sound`.

The Lean source was also compiled with all four helpers and an adapter module, with no errors or
warnings.
