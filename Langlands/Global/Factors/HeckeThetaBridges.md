# Bridges from Hecke theta coefficients to adelic tensor coefficients

Worker 1692 supplies these internal bridges requested by Worker 1798 for the
global assembly. They connect the finite theta coefficients
(`HeckeThetaCoefficients`, package B3) and their Fourier counterparts
(`HeckeFourierTheta`, package B4) with the adelic tensor coefficients
`Hecke.tensorCoeff` and the local Fourier transforms `Hecke.localFourier` of
Worker 1798's Poisson module `AdelicPoisson`. They also add analytic facts
about the class factors and the dual mixed character. Everything concerns an
actual Hecke character `χ` of a number field `K` in unrestricted universe `u`,
with the actual local Euler tests, uniformizers `π_v`, finite divisors `d`,
supplied finite unitary additive characters `ψf v` and self-dual Haar measures
`μ v`. Recall that `Hecke.tensorCoeff S g γ` is `∏_{v ∈ S} g_v(γ)` when `γ`
is integral at every finite place outside `S`, and `0` otherwise.

## Tensor coefficients (namespace `Langlands.Global.HeckeTheta`)

- `coe_dilatedEulerTest`: the Schwartz–Bruhat function `dilatedEulerTest χ d v`
  of B4 is the function `x ↦ eulerTest_v(x π_v^(d v))`.
- `fourierDilatedEulerTest χ ψf μ d v` is the function
  `Hecke.localFourier ψf μ v (dilatedEulerTest χ d v)`, the actual local Fourier
  transform (for `ψf v` and `μ v`) of the dilated Euler test;
  `fourierDilatedEulerTest_eq` records this as an equality of families.
- `thetaCoeff_eq_tensorCoeff`: for every finite set `S` containing the support
  of `d` and every finite place where `χ_v` has nonzero multiplicative
  conductor, `thetaCoeff χ d γ = Hecke.tensorCoeff S (dilatedEulerTest χ d) γ`
  for all `γ ∈ K`. Outside `S` the theta factor is the unramified Euler test at
  `γ` (since `d(v) = 0`). This is `1` when `γ` is integral at `v`, which gives
  the finite product over `S`. If `γ` is not integral at some `v ∉ S`, that
  factor vanishes, so the coefficient is `0`.
- `fourierThetaCoeff_eq_tensorCoeff`: if `S` moreover contains every place where
  the additive conductor of `ψf v` is nonzero, then
  `fourierThetaCoeff χ ψf μ d w = Hecke.tensorCoeff S (fourierDilatedEulerTest χ ψf μ d) w`
  for all `w ∈ K`. Outside `S` both conductors and `d(v)` vanish, so the
  Fourier factor is the Euler test itself (`fourierEulerTest_eq_eulerTest`).
  Inside `S` the factors are the local Fourier transforms of the dilated tests
  (`fourierThetaFactor_eq_fourierTransform`).

## Class factors

- `differentiable_classFactor` and `differentiable_dualClassFactor`: both are
  entire, as finite products of integer powers of nowhere-vanishing entire
  functions of `s` (the spectral variables are complex exponentials).
- `classFactor_ne_zero`: the class factor never vanishes.
- `classFactor_one_sub_mul_dualClassFactor`:
  `classFactor χ d (1 - s) · dualClassFactor χ d s = 1`, which is the B4 identity
  `dualClassFactor_one_sub_mul_classFactor` at `1 - s`.

## Dual mixed character (namespace `Langlands.Global.HeckeFunctionalEquation`)

Let `dR`, `dC` present the infinite components of `χ` and `dR'`, `dC'` those of
`χ⁻¹`, all as hypotheses in the target's sense. Write `χV` and `χV'` for the
corresponding `Hecke.mixedCharFun`.

- `mixedCharFun_dual_eq_inv_apply`: `χV' y = χV (y⁻¹)` for every `y` in the
  mixed space. By the package A uniqueness lemmas, `dR'` has the parities of `dR`
  and opposite exponents, and `dC'` has opposite weights and exponents. The
  Library identity `Hecke.mixedCharFun_inv` then concludes.
- `mixedCharFun_dual_eq_inv`: if the mixed norm of `y` is nonzero, then
  `χV' y = (χV y)⁻¹`. Each real coordinate is then nonzero, and there the sign
  `x/|x|` is its own inverse and `|x|^(-t) = (|x|^t)⁻¹`. At complex coordinates,
  `(z/|z|)^(-N) = ((z/|z|)^N)⁻¹` and `|z|^(-2u) = (|z|^(2u))⁻¹` hold for all `z`.

These results do not prove the Poisson summation, unit unfolding, analytic
continuation or the global functional equation.
