# Proper submodules of strictly dominant principal series lie in the kernel of the Jacquet integral

Lean module: `Langlands.Representation.Archimedean.JacquetKernel`.

Let `χ` be a strictly dominant signed power (module `PartialJacquetIntegral`). This module shows
that every proper `(𝔤, K)`-stable subspace `W` of the `O(n)`-finite principal series `X(χ)` of
`GL_n(ℝ)` lies in the kernel of the Jacquet integral `Λ_n` (`jacquet_eq_zero_of_proper`). The
proof passes to the annihilator of `W` in the dual principal series and applies
`JacquetDual.jacquet_eq_zero`.

Declarations without a prefix are in the namespace `Langlands.Archimedean.JacquetKernel`.

## Linearity of `Λ_n`

* `jacquet_smul`: `Λ_n(c h) = c Λ_n(h)` for all `h`.
* `jacquet_add`: `Λ_n(h₁ + h₂) = Λ_n(h₁) + Λ_n(h₂)` for `h₁, h₂ ∈ X(χ)`. The step
  `jacquetStep_add` reduces, by the Iwasawa decomposition and `PartialJacquet.jacquetStep_mul`,
  to points of `O(m)`. There both integrals converge (`PartialJacquet.integrable_chart`).
  Recursion then uses `PartialJacquet.jacquetStep_mem`.
* `jacquetKernel n hχ he` is the subspace `{f ∈ X(χ) | Λ_n f = 0}`.

## The annihilator

`annihilator χ W hW` is the set of `u` in the `O(n)`-finite principal series of `χ⁻¹` with
`∫_{O(n)} u w = 0` for every `w ∈ W`.

* It is stable under right translation by `O(n)` (`annihilator_rightTranslation`), by right
  invariance of `haarK` and `R(k⁻¹) W ⊆ W`.
* It is stable under right derivatives (`annihilator_rightDerivative`). The product `u w` is
  smooth and modulus-equivariant (Library `isModulusEquivariant_mul`), so the Library's
  `integral_rightDerivative_eq_zero` and the product rule `rightDerivative_mul_fun` give
  `∫ R(X)u · w = −∫ u · R(X)w = 0`.
* It is nonzero if `W ≠ X(χ)` (`annihilator_ne_bot`). The accepted
  `PrincipalSeriesAnnihilator.exists_orthogonal` gives `v ∈ X(χ)`, nonzero on `O(n)`, with
  `∫ w · conj(v) = 0` for all `w ∈ W`. On `O(n)`, `v` is a polynomial `P` in the matrix entries
  (`OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors`). Hence `conj(v)` is
  the polynomial with conjugated coefficients (`conj_eval_ofReal`), and it is `O(n)`-finite by
  `TranslateFinite.finiteDimensional_span_eval`. It transforms under diagonal sign matrices by
  the character of `χ⁻¹`, because sign values of `χ` have norm `1` (`conj_eq_inv_of_norm_eq_one`,
  `principalSeriesCharacter_sign`). The accepted extension lemma
  `PrincipalSeriesExtension.extension_mem_kFiniteFunctions` extends `conj(v)` to a nonzero
  element of the annihilator.

## Proper submodules

`jacquet_eq_zero_of_proper`: if `W ≤ X(χ)` is stable under `O(n)` and under all right
derivatives, and some `f ∈ X(χ)` is not in `W`, then `W ≤ jacquetKernel`. The annihilator is a
nonzero `(𝔤, K)`-stable subspace of the dual principal series orthogonal to every `w ∈ W`, so
`JacquetDual.jacquet_eq_zero` gives `Λ_n(w) = 0`.
