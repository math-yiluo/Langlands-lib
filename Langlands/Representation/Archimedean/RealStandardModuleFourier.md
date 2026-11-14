# Fourier conditions of real standard modules under right translation and right derivatives

Module: `Langlands.Representation.Archimedean.RealStandardModuleFourier`.

## Purpose and provenance

This module contains internal infrastructure for proving
`Langlands.Archimedean.RealLanglandsQuotientStatement`, the existence half of the Langlands
classification for `(𝔤𝔩_n(ℝ), O(n))`-modules (Knapp 1994, Theorem 1). That statement asks for an
intertwiner `B` with `IsRealStandardIntertwiner`. This condition requires the `O(n)`-finite
functions of `realStandardModule n ds` to be closed under right translation by `O(n)` and under
right derivatives `rightDerivative (matrixModel ℝ n) X`.

`realStandardModule N ds` is the set of functions `f` in the smooth principal series
`principalSeries ℝ N (realPositionCharacter ds)` that also satisfy Fourier conditions. For each
two-dimensional block at position `p` with weight `d.weight`, the block Fourier coefficient
`blockFourierCoefficient N p k f g` must vanish for all `g` and all `|k| < |d.weight|`. The coefficient is
`∫ θ in 0..2π, f(r_p(θ) g) e^{-ikθ}`, with `r_p(θ) = blockRotation N p θ`. This module proves that
both operations preserve these Fourier conditions. Preserving membership in the principal series is a
separate, field-general fact, so the main results take it as a hypothesis.

The mathematical content is elementary. The rotations act on the left and translations and
derivatives act on the right, so they commute. The Fourier coefficient of a right derivative is the
derivative of the Fourier coefficient, by differentiation under the integral sign. The module makes
no literature assertion beyond this, so it has no literature sources.

## Declarations

### Matrix exponential as a unit

- `matrixExpUnit N X : Langlands.GeneralLinear N ℝ` is the matrix exponential `exp X`, an element
  of `GL_N(ℝ)` with inverse `exp(-X)`.
- `matrixExpUnit_val`: its underlying matrix is `NormedSpace.exp X`.
- `matrixExpUnit_zero`: `matrixExpUnit N 0 = 1`.
- `matrixExpUnit_add_smul`: `exp((s + t) X) = exp(s X) exp(t X)`.
- `contDiff_exp_smul`: `s ↦ exp(s X)` is a smooth (`C^∞`) map `ℝ → M_N(ℝ)`. The proof uses the
  analyticity of the exponential on all of `M_N(ℝ)`, since its radius of convergence is infinite.
- `contMDiff_matrixExpUnit_smul`, `contMDiff_blockRotation`: `s ↦ exp(s X)` and `θ ↦ r_p(θ)` are
  smooth maps `ℝ → GL_N(ℝ)` for the Library's manifold structure `matrixModel ℝ N`. The proof
  reduces to the matrix-valued statement through the open embedding `Units.val`.
- `hasMFDerivAt_matrixExpUnit_smul`: the manifold derivative of `s ↦ exp(s X)` at `s = 0` is
  `t ↦ t X`.
- `hasDerivAt_mul_matrixExpUnit_smul`: if `f : GL_N(ℝ) → ℂ` is `C¹`, then `s ↦ f(h exp(s X))`
  has derivative `rightDerivative (matrixModel ℝ N) X f h` at `s = 0`. The proof applies the
  chain rule for manifold derivatives to `u ↦ f(h u)` and `s ↦ exp(s X)`.

### Differentiation under the integral sign

- `hasDerivAt_intervalIntegral_of_contDiff`: let `Φ : ℝ × ℝ → ℂ` be `C¹`, and let `Φ' θ` be the
  derivative of `s ↦ Φ(s, θ)` at `s₀` for every `θ`. Then `s ↦ ∫ θ in a..b, Φ(s, θ)` has derivative
  `∫ θ in a..b, Φ' θ` at `s₀`. The proof applies Mathlib's
  `intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le` with the partial derivative
  `fderiv ℝ Φ (s, θ) (1, 0)`. The constant bound is that partial derivative's maximum on the
  compact set `closedBall s₀ 1 ×ˢ uIcc a b`, which exists because the partial derivative is
  continuous. `Φ'` is then identified with the partial derivative by uniqueness of derivatives.
- `contMDiff_blockRotation_mul_mul_matrixExpUnit`: `(s, θ) ↦ r_p(θ) g exp(s X)` is a smooth map
  `ℝ × ℝ → GL_N(ℝ)`.
- `contDiff_blockFourierIntegrand`: for smooth `f`, the function
  `(s, θ) ↦ f(r_p(θ) g exp(s X)) e^{-ikθ}` is smooth on `ℝ × ℝ`.

### Fourier coefficients

- `blockFourierCoefficient_rightTranslation`: the coefficient of the right translate
  `Whittaker.rightTranslation ℂ _ s f = f(· s)` at `g` equals the coefficient of `f` at `g s`.
  Proof: `r_p(θ) g s = r_p(θ) (g s)` under the integral.
- `blockFourierCoefficient_rightDerivative_eq_zero`: let `f` be smooth, and suppose
  `blockFourierCoefficient N p k f g = 0` for every `g`. Then the same holds for
  `rightDerivative (matrixModel ℝ N) X f` for every `X`. Proof: for fixed `g`, the function
  `s ↦ ∫ θ in 0..2π, f(r_p(θ) g exp(s X)) e^{-ikθ}` is the coefficient of `f` at `g exp(s X)`,
  so it is identically zero. By the previous two items and `hasDerivAt_mul_matrixExpUnit_smul`
  (applied with `h = r_p(θ) g`), its derivative at `0` is
  `∫ θ in 0..2π, (rightDerivative X f)(r_p(θ) g) e^{-ikθ}`. This is the coefficient of
  `rightDerivative X f` at `g`, and it is zero because the derivative of a constant is zero.

### Membership in `realStandardModule`

- `realStandardModule_le_principalSeries`: `realStandardModule N ds` is contained in
  `principalSeries ℝ N (realPositionCharacter ds)`.
- `rightTranslation_mem_realStandardModule`: suppose `f ∈ realStandardModule N ds` and its right
  translate by `s ∈ GL_N(ℝ)` lies in `principalSeries ℝ N (realPositionCharacter ds)`. Then the right
  translate lies in `realStandardModule N ds`. The Fourier conditions follow from
  `blockFourierCoefficient_rightTranslation`.
- `rightDerivative_mem_realStandardModule`: suppose `f ∈ realStandardModule N ds` and
  `rightDerivative (matrixModel ℝ N) X f` lies in the principal series. Then the right derivative
  lies in `realStandardModule N ds`. The Fourier conditions follow from
  `blockFourierCoefficient_rightDerivative_eq_zero`, using the smoothness of `f`, which is part of
  principal-series membership.

## Use

Suppose another module shows that the `unitaryCompact ℝ N`-finite part of the principal series is
stable under right translation by `unitaryCompact ℝ N` and under right derivatives. The last two
lemmas then give the same stability for `kFiniteFunctions (realStandardModule N ds)
(unitaryCompact ℝ N)`, which is `realStandardModule N ds ⊓ kFiniteVectors …`.
