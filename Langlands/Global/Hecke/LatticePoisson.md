# Poisson summation on `ℤ^ι`

Module `Langlands.Global.Hecke.LatticePoisson`, namespace `Langlands.Global.Hecke`.

This module proves the multi-dimensional Poisson summation formula for the standard lattice
`ℤ^ι ⊂ ℝ^ι` (with `ι` a finite type), for continuous functions whose integer translates are
locally uniformly summable. It is the analytic input of the global (Tate–Hecke) theta
functional equation used for the functional equation of Hecke `L`-functions; the lattices of a
number field are reduced to `ℤ^ι` by a choice of `ℤ`-basis in later modules.

## Provenance

Internal. Poisson summation on `ℤ^n` is classical; the formulation here follows the
one-dimensional Mathlib theorem `Real.tsum_eq_tsum_fourier` and its proof
(Mathlib `Analysis/Fourier/PoissonSummation.lean`), using Mathlib's multi-dimensional Fourier
series on the torus `UnitAddTorus ι = ι → ℝ/ℤ` (`Analysis/Fourier/AddCircleMulti.lean`). No
conventions beyond those of Mathlib are introduced: `𝐞 t = exp(2πit)` is `Real.fourierChar`,
and the Fourier transform uses the kernel `e(-m · y)` and Lebesgue measure `volume` on
`ι → ℝ`.

## Definitions

- `intVec n : ι → ℝ` — the integer vector `n : ι → ℤ` viewed as a real vector.
- `intDot m x = ∑ i, m i * x i` — the pairing of an integer frequency `m : ι → ℤ` with
  `x : ι → ℝ`.
- `intFourier f m = ∫ y, 𝐞 (-intDot m y) • f y` — the Fourier transform of
  `f : (ι → ℝ) → ℂ` (for Lebesgue measure) evaluated at the integer frequency `m`. It is the
  Bochner integral, hence `0` when the integrand is not integrable.
- `torusMk x` — the image of `x : ι → ℝ` in the torus `UnitAddTorus ι`, coordinatewise; and
  `torusMkCM`, the same map as a continuous map.
- `unitBox ι = (0, 1]^ι`, the half-open unit box (the domain used by Mathlib's
  `UnitAddTorus.mFourierCoeff_eq_integral` with base point `0`), and `iccBox ι = [0, 1]^ι` as a
  compact set.
- `intLatticeEquiv` — the bijection between `ι → ℤ` and the `ℤ`-span of the standard basis of
  `ι → ℝ` (as an additive subgroup), with a `Countable` instance on the latter.
- `periodization f = ∑' n, f.comp (addRight (intVec n))` for `f : C(ι → ℝ, ℂ)`, a sum in the
  space of continuous maps with the compact-open topology (it is `0` if this family is not
  summable).
- `torusPeriodization f : C(UnitAddTorus ι, ℂ)` — the descent of `periodization f` to the
  torus, via the quotient map `torusMkCM`.

## Main results

All results take `f : C(ι → ℝ, ℂ)` and the hypothesis

`hf : ∀ K : Compacts (ι → ℝ), Summable fun n => ‖(f.comp (addRight (intVec n))).restrict K‖`,

i.e. the integer translates of `f` are uniformly summable on every compact set.

- `mFourierCoeff_torusPeriodization hf m` :
  `UnitAddTorus.mFourierCoeff (torusPeriodization f) m = intFourier f m`.
- `hasSum_intFourier_mul_fourierChar hf h_sum x`, for `h_sum : Summable (intFourier f)`:
  `HasSum (fun m => intFourier f m * 𝐞 (intDot m x)) (∑' n, f (x + intVec n))`.
- `tsum_add_intVec_eq_tsum_intFourier hf h_sum x` (**Poisson summation**):
  `∑' n, f (x + intVec n) = ∑' m, intFourier f m * 𝐞 (intDot m x)`.

Auxiliary results: `intDot_intVec`, `intDot_neg`, `intDot_add`, `fourierChar_intCast`
(`𝐞 k = 1` for integers `k`), `mFourier_torusMk` (the torus character `mFourier m` at
`torusMk x` is `𝐞 (intDot m x)`), `fourierChar_neg_intDot_add_intVec` (the kernel is
`ℤ^ι`-periodic), `unitBox_ae_eq_fundamentalDomain`, `lintegral_eq_tsum_unitBox` and
`integral_eq_tsum_unitBox` (unfolding an integral over `ι → ℝ` into a sum over translates of
the unit box, for nonnegative functions and for integrable functions respectively),
`torusMk_eq_torusMk` (equal images in the torus differ by an integer vector),
`periodization_apply` (pointwise evaluation when the translates are summable in
`C(ι → ℝ, ℂ)`), `periodization_add_intVec`, `periodization_factorsThrough`,
`torusPeriodization_torusMk`, and `integrable_of_summable_norm_box` (if the sup norms of the
translates on `[0,1]^ι` are summable then `f` is integrable).

## Proof

1. *Lattice unfolding.* The box `(0,1]^ι` agrees almost everywhere with Mathlib's
   `ZSpan.fundamentalDomain` of the standard basis (both are products of intervals with the same
   closure, `Measure.univ_pi_Ioc_ae_eq_Icc`, `Measure.univ_pi_Ico_ae_eq_Icc`).
   `ZSpan.isAddFundamentalDomain'` and `IsAddFundamentalDomain.integral_eq_tsum'` (resp.
   `lintegral_eq_tsum'`) then write `∫ h` as a sum over the lattice of integrals over the
   box; the lattice is reindexed by `ι → ℤ` through `intLatticeEquiv` and negation.
2. *Periodization.* Local uniform summability gives summability in `C(ι → ℝ, ℂ)`
   (`ContinuousMap.summable_of_locally_summable_norm`), so `periodization f` evaluates
   pointwise to `∑' n, f (x + intVec n)`. Shifting the index by `k` shows it is
   `ℤ^ι`-periodic, and since `torusMkCM` is a quotient map (a product of the open quotient maps
   `ℝ → ℝ/ℤ`), it descends to the continuous function `torusPeriodization f`.
3. *Integrability.* Cover `ι → ℝ` by the compact boxes `[n, n+1]^ι` of volume `1`; the sup
   norm of `f` on `[n, n+1]^ι` equals that of the `n`-th translate on `[0,1]^ι`, so Mathlib's
   `integrable_of_summable_norm_restrict` gives integrability of `f`, and likewise of
   `y ↦ 𝐞 (-m·y) • f y` (the character has modulus one).
4. *Fourier coefficients.* By `UnitAddTorus.mFourierCoeff_eq_integral` the `m`-th coefficient
   is `∫_{(0,1]^ι} 𝐞(-m·x) • ∑' n, f (x + n)`. The sum is pulled out of the integral by
   `integral_tsum_of_summable_integral_norm`, the integral of each summand being bounded by the
   sup norm of the translate on `[0,1]^ι` times the volume of the box. Periodicity of the
   kernel turns each summand into `∫_{(0,1]^ι} g (x + n)` with `g y = 𝐞(-m·y) • f y`, and step 1
   reassembles the sum to `∫ g = intFourier f m`.
5. *Poisson summation.* With summable Fourier coefficients, Mathlib's
   `UnitAddTorus.hasSum_mFourier_series_apply_of_summable` gives pointwise convergence of the
   Fourier series of `torusPeriodization f` at `torusMk x`; rewriting the coefficients by
   step 4, the characters by `mFourier_torusMk` and the value by
   `torusPeriodization_torusMk` and `periodization_apply` yields the `HasSum` statement, and
   `HasSum.tsum_eq` gives the equality of sums.
