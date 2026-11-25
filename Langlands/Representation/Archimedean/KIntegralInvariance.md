# `GL_n(ℝ)`-invariance of the `O(n)`-integral on modulus-equivariant functions

Lean module: `Langlands.Representation.Archimedean.KIntegralInvariance`.

The Library's `RealPrincipalSeriesDualityProof` proves the infinitesimal invariance
`∫_{O(n)} (R(X) φ)(k) dk = 0` of the `O(n)`-integral. It holds for every smooth function `φ` on
`GL_n(ℝ)` that transforms on the left by the modulus character of the upper triangular Borel
subgroup (`RealPrincipalSeriesDuality.integral_rightDerivative_eq_zero`). This module integrates
that to invariance under the whole group: `∫_{O(n)} φ(k g) dk = ∫_{O(n)} φ(k) dk` for every
`g ∈ GL_n(ℝ)`. The statement is `Langlands.Archimedean.KIntegralInvarianceStatement`, proved as
`Langlands.Archimedean.kIntegralInvariance`.

In the proof of `RealStandardLanglandsQuotientStatement` (through the module
`MaximalParabolicIntegration`) it is used for the
Levi subgroup `GL_{n-1}(ℝ)` of the maximal parabolic subgroup `P_{n-1,1}`: averaging over `O(n-1)`
turns a modulus-equivariant function for the Borel subgroup into one for `P_{n-1,1}`.

Notation: `GL_n(ℝ)` is `Langlands.GeneralLinear n ℝ`, `O(n)` is the subgroup `unitaryCompact ℝ n`,
and `R(X)` is `rightDerivative (matrixModel ℝ n) X`. `RealPrincipalSeriesDuality.haarK n` is the
normalized Haar measure on `O(n)` for its Borel σ-algebra `measurableSpaceK n` (both from the
Library). `RealPrincipalSeriesDuality.IsModulusEquivariant φ` means
`φ(exp(diag x) u g) = exp(∑_i (n - 1 - 2i) x_i) φ(g)` for real `x`, `u` upper unipotent and `g`
(the modulus character on the positive diagonal torus). `matrixExpUnit n X` (Library,
`RealStandardModuleFourier`) is the matrix exponential as an element of `GL_n(ℝ)`.
`MatrixCoefficientAnalytic.expDiagonal` and `MatrixCoefficientAnalytic.exists_kak` are from the
Library module `PrincipalSeriesMatrixCoefficientAnalytic`. Declarations without a prefix are in the
namespace `Langlands.Archimedean.KIntegralInvariance`.

## The statement

`KIntegralInvarianceStatement`: for every `n`, every `φ : GL_n(ℝ) → ℂ` that is smooth
(`ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ φ`) and satisfies `IsModulusEquivariant φ`, and every
`g ∈ GL_n(ℝ)`,

`∫ k, φ(k g) d(haarK n) = ∫ k, φ(k) d(haarK n)`.

Products `f h` of smooth functions in principal series of pointwise inverse characters satisfy
the hypotheses (Library `RealPrincipalSeriesDuality.isModulusEquivariant_mul`). So the statement
gives the `GL_n(ℝ)`-invariance of the standard pairing `∫_{O(n)} f h`.

Provenance. Derived, internal infrastructure. That the `K`-integral is a `G`-invariant functional
on the principal series induced from the modulus character is standard (it is the
`G`-invariant integral over `B \ G`). The proof here derives it from the Library's infinitesimal
version and makes no further literature assertion.

## Proof

1. **Translates** (`isModulusEquivariant_rightTranslation`). If `φ` is modulus-equivariant, so is
   `x ↦ φ(x h)` for every `h`.
2. **Conjugating the direction** (`matrixExpUnit_conj`, `rightDerivative_mul_eq`). Since
   `exp(s · h X h⁻¹) = h exp(s X) h⁻¹` (`Matrix.exp_conj`), the derivatives at `0` of
   `s ↦ φ(k h exp(sX))` and of `s ↦ φ(k exp(s · hXh⁻¹) h)` agree. So
   `(R(X) φ)(k h) = (R(h X h⁻¹) φ_h)(k)` with `φ_h(x) = φ(x h)`. Both derivatives come from the
   Library's `hasDerivAt_mul_matrixExpUnit_smul`.
3. **Constancy along one-parameter subgroups** (`integral_mul_matrixExpUnit_eq`). Let
   `ψ(t) = ∫ φ(k g exp(tX)) dk`. Differentiation under the integral sign
   (`hasDerivAt_integral_of_dominated_loc_of_deriv_le`) gives
   `ψ'(t) = ∫ (R(X) φ)(k g exp(tX)) dk`. The pointwise derivative is
   `hasDerivAt_mul_matrixExpUnit_at`. The bound comes from continuity of
   `(t, k) ↦ (R(X)φ)(k g exp(tX))` on the compact set `closedBall t₀ 1 × O(n)`, using the Library's
   `contMDiff_rightDerivative` and `contMDiff_matrixExpUnit_smul`. By step 2 with
   `h = g exp(tX)`, `ψ'(t) = ∫ (R(h X h⁻¹) φ_h)(k) dk`. This is `0` by
   `integral_rightDerivative_eq_zero` and step 1. Hence `ψ` is constant
   (`is_const_of_deriv_eq_zero`), and `ψ(t) = ψ(0)`.
4. **`KAK`** (`integral_mul_eq`). Write `g = k₁ · expDiagonal h 1 · k₂` (`exists_kak`). Here
   `expDiagonal h 1 = exp(1 · diag h)` (`expDiagonal_one_eq`, via the Library's
   `matrixExpUnit_diagonal`). With `φ₂(x) = φ(x k₂)`:
   `∫ φ(k g) = ∫ φ₂(k k₁ exp(diag h)) = ∫ φ₂(k k₁) = ∫ φ₂(k) = ∫ φ(k)`. These use step 3, then right
   invariance of `haarK n` (Library instance `isMulRightInvariant_haarK`,
   `integral_mul_right_eq_self`) twice.
