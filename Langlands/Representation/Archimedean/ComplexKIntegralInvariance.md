# `GL_n(ℂ)`-invariance of the `U(n)`-integral on modulus-equivariant functions

Lean module: `Langlands.Representation.Archimedean.ComplexKIntegralInvariance`.

This module is infrastructure for the proof of
`ComplexStandardLanglandsQuotientStatement`. It is the complex counterpart of the Library module
`KIntegralInvariance` (for `GL_n(ℝ)`).

For every smooth function `φ` on `GL_n(ℂ)` that transforms on the left under the upper triangular
Borel subgroup by its modulus character, the integral of `φ` over `U(n)` is invariant under right
translation by all of `GL_n(ℂ)`: `∫_{U(n)} φ(k g) dk = ∫_{U(n)} φ(k) dk`. The statement is
`Langlands.Archimedean.ComplexKIntegralInvarianceStatement`, proved as
`Langlands.Archimedean.complexKIntegralInvariance`. In the proof of
`ComplexStandardLanglandsQuotientStatement` it is applied to Levi subgroups of maximal parabolic
subgroups, as in the real case (integration formula for `P_{n-1,1}`).

Notation: `GL_n(ℂ)` is `Langlands.GeneralLinear n ℂ`, `U(n)` is the subgroup `unitaryCompact ℂ n`
with the Library's Haar probability measure `ComplexDuality.unitaryHaar n`. `principalSeries ℂ n χ`
and `principalSeriesCharacter` are the Library's: `f ∈ principalSeries ℂ n χ` means `f` is smooth and
`f(diag(a) u g) = ∏ᵢ χᵢ(aᵢ) (|aᵢ|²)^((n-1)/2 - i) f(g)` for `u` upper unipotent.
`rightDerivative (matrixModel ℂ n) X` is the right derivative `R(X)`. `unitsExtension φ` is the
Library's extension of `φ` to all matrices by `0` off the invertible ones. Declarations without a
prefix are in the namespace `Langlands.Archimedean.ComplexKIntegralInvariance`; `pairTerm`,
`fderiv_mul_eq_sum_pairTerm`, `integral_fderiv_mul_eq_zero`, `coeffRe`, `coeffIm`, `skewRe`,
`skewIm`, `continuous_fderiv_apply_val` are from the Library namespace
`ComplexDuality.LieInvariance`; `expDiag`, `hasDerivAt_mul_expDiag_at` and `exists_kak`
are from `ComplexMatrixCoefficientAnalytic`.

## Definitions

* `modulusCharacter n i z = (|z|²)^((n-1)/2 - i)`. The principal series of these characters
  consists of the smooth `φ` with `φ(diag(a) u g) = ∏ᵢ |aᵢ|^(2(n-1-2i)) φ(g)`, i.e. left
  equivariance by the modulus character of the upper triangular Borel subgroup
  (`modulus_mul_eq`: `principalSeriesCharacter ℂ n (modulusCharacter n) a` is the product
  `∏ᵢ (|aᵢ|²)^((n-1)/2-i) (|aᵢ|²)^((n-1)/2-i)` used by the Library's `LieInvariance`).
* `translateExtension φ g y = unitsExtension φ (y g)`: the extension of the right translate by `g`.

## The statement

`ComplexKIntegralInvarianceStatement`: for every `n`, every
`φ ∈ principalSeries ℂ n (modulusCharacter n)` and every `g ∈ GL_n(ℂ)`,

`∫ k, φ(k g) d(unitaryHaar n) = ∫ k, φ(k) d(unitaryHaar n)`.

Products `f h` of smooth functions of principal series with pointwise inverse characters satisfy
the hypothesis, so the statement gives the `GL_n(ℂ)`-invariance of the integration pairing
`∫_{U(n)} f h`.

Provenance. Derived, internal infrastructure. That the `K`-integral is a `G`-invariant functional on
the principal series induced from the modulus character is standard (it is the `G`-invariant
integral over `B \ G`). The proof derives it from the Library's pointwise identity behind the
infinitesimal invariance of the pairing (`ComplexDuality.LieInvariance`); no further literature
assertion.

## Proof

1. **Infinitesimal invariance for a general function** (`integral_fderiv_eq_zero`). Let `Φ` be
   smooth on the invertible matrices, invariant under left multiplication by upper unipotent
   matrices, and transforming under left multiplication by `diag(a)` by the modulus character.
   Then `∫_{U(n)} DΦ(k)(k X) dk = 0` for every complex matrix `X` and every left invariant finite
   measure. The Library's `fderiv_mul_eq_sum_pairTerm` writes `DΦ(k)(k X)` pointwise as a sum of
   pair terms, each the sum of derivatives of `Re Z_ab Φ` and `Im Z_ab Φ` along skew-Hermitian
   directions `Y k`; each pair term integrates to `0` by `integral_fderiv_mul_eq_zero` (left
   invariance of the measure). This is the argument of the Library's
   `integral_rightDerivative_mul_add_eq_zero`, with `Φ` in place of the product of two
   principal-series functions.
2. **Translates** (`translateExtension_contDiffOn`, `translateExtension_unipotent`,
   `translateExtension_diagonal`). For `φ` in the principal series of the modulus character and
   any `y ∈ GL_n(ℂ)`, `translateExtension φ y` satisfies the hypotheses of step 1, because left
   multiplications commute with right multiplication by `y`.
3. **Conjugating the direction** (`rightDerivative_eq_fderiv_translate`). By the Library's
   `rightDerivative_eq_fderiv` and the chain rule for `z ↦ z y`,
   `(R(X) φ)(k y) = D(translateExtension φ y)(k)(k · y X y⁻¹)`.
4. **Constancy along real diagonal one-parameter subgroups** (`integral_mul_expDiag_eq`). Let
   `ψ(t) = ∫ φ(k g expDiag h t) dk`. Differentiation under the integral sign
   (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`; pointwise derivative
   `hasDerivAt_mul_expDiag_at`; bound from continuity of `(t, k) ↦ (R(H)φ)(k g expDiag h t)` on the
   compact `closedBall t₀ 1 × U(n)`, with `t ↦ expDiag h t` continuous since its inverse is
   `expDiag h (-t)`) gives `ψ'(t) = ∫ (R(H)φ)(k g expDiag h t) dk`, which is `0` by steps 3 and 1
   with `y = g expDiag h t`. So `ψ` is constant and `ψ(t) = ψ(0)`.
5. **`KAK`** (`integral_mul_eq`). Write `g = k₁ expDiag h 1 k₂` (`exists_kak`). The right translate
   `φ₂(x) = φ(x k₂)` is again in the principal series (Library
   `rightTranslation_mem_principalSeries`). Then
   `∫ φ(k g) = ∫ φ₂(k k₁ expDiag h 1) = ∫ φ₂(k k₁) = ∫ φ₂(k) = ∫ φ(k)`, by step 4 and right
   invariance of `unitaryHaar n` (twice).
