import Langlands.LocalFactor.Archimedean.RealTateZeta
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod

/-! # Tate's identity for real zeta integrals

For Schwartz functions `f, h` on `ℝ`, a parity `e` and `0 < Re u < 1`,
`Z(f, e, u) Z(ĥ, e, 1 - u) = Z(f̂, e, 1 - u) Z(h, e, u)`, where `ĥ = 𝓕⁻ h`, i.e.
`ĥ(y) = ∫ exp(2π i x y) h(x) dx`. Both sides equal `∫ k(z) ∫ f(x) ĥ(x z) dx dz` with
`k(z) = sgn(z)^e |z|^(-u)`, by the substitution `y = x z` and Fubini's theorem, and the inner
integral is symmetric in `(f, h)` by a second application of Fubini's theorem.
See the paired Markdown.
-/

noncomputable section

open MeasureTheory Filter Set Complex Function
open scoped SchwartzMap FourierTransform Real

namespace Langlands.LocalFactor.RealTate

/-- The kernel `z ↦ sgn(z)^e |z|^(-u)`, set to `0` at `z = 0`. -/
def kern (e : Fin 2) (u : ℂ) (z : ℝ) : ℂ :=
  integrand (fun _ => 1) e (1 - u) z

theorem measurable_kern (e : Fin 2) (u : ℂ) : Measurable (kern e u) :=
  measurable_integrand measurable_const e (1 - u)

/-- The substitution identity behind Tate's argument: for `x ≠ 0`,
`(f(x) sgn(x)^e |x|^(u-1)) · |x| · (φ(xz) sgn(xz)^e |xz|^(-u)) = f(x) φ(xz) k(z)`. -/
theorem integrand_mul_abs_mul_integrand (f φ : ℝ → ℂ) (e : Fin 2) (u : ℂ) {x : ℝ} (hx : x ≠ 0)
    (z : ℝ) :
    integrand f e u x * (((|x| : ℝ) : ℂ) * integrand φ e (1 - u) (x * z)) =
      f x * φ (x * z) * kern e u z := by
  by_cases hz : z = 0
  · simp [hz, kern, integrand_zero]
  · have hxz : x * z ≠ 0 := mul_ne_zero hx hz
    simp only [kern, integrand, hx, hz, hxz, ↓reduceIte]
    rw [sign_mul, abs_mul, ofReal_mul, mul_cpow_ofReal_nonneg (abs_nonneg x) (abs_nonneg z),
      mul_pow]
    have hA : ((|x| : ℝ) : ℂ) ≠ 0 := abs_cpow_ne_zero hx
    have hs := sign_pow_mul_self hx e
    have hp : ((|x| : ℝ) : ℂ) ^ (u - 1) * ((|x| : ℝ) : ℂ) ^ (1 - u - 1) *
        ((|x| : ℝ) : ℂ) = 1 := by
      rw [← cpow_add _ _ hA, show u - 1 + (1 - u - 1) = -1 by ring, cpow_neg_one,
        inv_mul_cancel₀ hA]
    set A := ((|x| : ℝ) : ℂ)
    set B := ((|z| : ℝ) : ℂ)
    set Sx := ((x / |x| : ℝ) : ℂ)
    set Sz := ((z / |z| : ℝ) : ℂ)
    linear_combination (f x * φ (x * z) * Sz ^ e.val * B ^ (1 - u - 1) *
        (A ^ (u - 1) * A ^ (1 - u - 1) * A)) * hs +
      (f x * φ (x * z) * Sz ^ e.val * B ^ (1 - u - 1)) * hp

theorem abs_mul_abs_inv {x : ℝ} (hx : x ≠ 0) : |x| * |x⁻¹| = 1 := by
  rw [abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hx)]

theorem integrable_slice (f φ : ℝ → ℂ) (e : Fin 2) (u : ℂ)
    (hφ : Integrable (integrand φ e (1 - u))) {x : ℝ} (hx : x ≠ 0) :
    Integrable (fun z => f x * φ (x * z) * kern e u z) := by
  have h : (fun z => f x * φ (x * z) * kern e u z) = fun z =>
      integrand f e u x * (((|x| : ℝ) : ℂ) * integrand φ e (1 - u) (x * z)) :=
    funext fun z => (integrand_mul_abs_mul_integrand f φ e u hx z).symm
  rw [h]
  exact ((hφ.comp_mul_left' hx).const_mul _).const_mul _

theorem integral_slice (f φ : ℝ → ℂ) (e : Fin 2) (u : ℂ) {x : ℝ} (hx : x ≠ 0) :
    ∫ z, f x * φ (x * z) * kern e u z = integrand f e u x * zeta φ e (1 - u) := by
  have h : (fun z => f x * φ (x * z) * kern e u z) = fun z =>
      integrand f e u x * (((|x| : ℝ) : ℂ) * integrand φ e (1 - u) (x * z)) :=
    funext fun z => (integrand_mul_abs_mul_integrand f φ e u hx z).symm
  rw [h, integral_const_mul, integral_const_mul,
    Measure.integral_comp_mul_left (integrand φ e (1 - u)) x, Complex.real_smul,
    ← mul_assoc ((|x| : ℝ) : ℂ), ← ofReal_mul, abs_mul_abs_inv hx, ofReal_one, one_mul, zeta]

theorem integral_norm_slice (f φ : ℝ → ℂ) (e : Fin 2) (u : ℂ) {x : ℝ} (hx : x ≠ 0) :
    ∫ z, ‖f x * φ (x * z) * kern e u z‖ =
      ‖integrand f e u x‖ * ∫ y, ‖integrand φ e (1 - u) y‖ := by
  have h : (fun z => ‖f x * φ (x * z) * kern e u z‖) = fun z =>
      ‖integrand f e u x‖ * (|x| * ‖integrand φ e (1 - u) (x * z)‖) := by
    funext z
    rw [← integrand_mul_abs_mul_integrand f φ e u hx z, norm_mul, norm_mul, norm_real,
      Real.norm_eq_abs, abs_abs]
  rw [h, integral_const_mul, integral_const_mul,
    Measure.integral_comp_mul_left (fun y => ‖integrand φ e (1 - u) y‖) x, smul_eq_mul,
    ← mul_assoc |x|, abs_mul_abs_inv hx, one_mul]

/-- First half of Tate's identity: for `0 < Re u < 1`,
`Z(f, e, u) Z(φ, e, 1 - u) = ∫ (∫ f(x) φ(xz) dx) k(z) dz`. -/
theorem zeta_mul_zeta_eq_integral (f φ : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu0 : 0 < u.re)
    (hu1 : u.re < 1) :
    zeta f e u * zeta φ e (1 - u) = ∫ z, (∫ x, f x * φ (x * z)) * kern e u z := by
  have hf := integrable_integrand f e hu0
  have hφ : Integrable (integrand φ e (1 - u)) :=
    integrable_integrand φ e (by simp only [sub_re, one_re]; linarith)
  set F : ℝ → ℝ → ℂ := fun x z => f x * φ (x * z) * kern e u z with hF
  have hmeas : AEStronglyMeasurable (uncurry F) (volume.prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    exact ((f.continuous.measurable.comp measurable_fst).mul
      (φ.continuous.measurable.comp (measurable_fst.mul measurable_snd))).mul
      ((measurable_kern e u).comp measurable_snd)
  have hint : Integrable (uncurry F) (volume.prod volume) := by
    rw [integrable_prod_iff hmeas]
    constructor
    · filter_upwards [Measure.ae_ne volume 0] with x hx
      exact integrable_slice f φ e u hφ hx
    · refine (hf.norm.mul_const (∫ y, ‖integrand φ e (1 - u) y‖)).congr ?_
      filter_upwards [Measure.ae_ne volume 0] with x hx
      exact (integral_norm_slice f φ e u hx).symm
  calc zeta f e u * zeta φ e (1 - u) = ∫ x, ∫ z, F x z := by
        rw [zeta, ← integral_mul_const]
        refine integral_congr_ae ?_
        filter_upwards [Measure.ae_ne volume 0] with x hx
        exact (integral_slice f φ e u hx).symm
    _ = ∫ z, ∫ x, F x z := integral_integral_swap hint
    _ = _ := by
        congr 1
        funext z
        simp only [hF]
        rw [integral_mul_const]

/-! ### Symmetry of the inner integral -/

theorem norm_exp_two_pi_I_mul (t : ℝ) :
    ‖Complex.exp (2 * (π : ℂ) * I * (t : ℂ))‖ = 1 := by
  rw [show 2 * (π : ℂ) * I * (t : ℂ) = ((2 * π * t : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- The inverse Fourier transform of a Schwartz function on `ℝ`:
`𝓕⁻ h (y) = ∫ exp(2π i x y) h(x) dx`. -/
theorem fourierInv_apply_real (h : 𝓢(ℝ, ℂ)) (y : ℝ) :
    (𝓕⁻ h : 𝓢(ℝ, ℂ)) y =
      ∫ x : ℝ, Complex.exp (2 * (π : ℂ) * I * ((x * y : ℝ) : ℂ)) * h x := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq']
  congr 1
  funext x
  rw [smul_eq_mul, Real.inner_apply]
  congr 2
  push_cast
  ring

/-- The inner integral of Tate's identity is symmetric:
`∫ f(x) ĥ(xz) dx = ∫ h(w) f̂(wz) dw`. -/
theorem integral_mul_fourierInv_mul (f h : 𝓢(ℝ, ℂ)) (z : ℝ) :
    ∫ x, f x * (𝓕⁻ h : 𝓢(ℝ, ℂ)) (x * z) = ∫ w, h w * (𝓕⁻ f : 𝓢(ℝ, ℂ)) (w * z) := by
  set Φ : ℝ → ℝ → ℂ := fun x w =>
    f x * (Complex.exp (2 * (π : ℂ) * I * ((w * (x * z) : ℝ) : ℂ)) * h w) with hΦ
  have hcont : Continuous (uncurry Φ) := by
    simp only [hΦ, uncurry_def]
    fun_prop
  have hint : Integrable (uncurry Φ) (volume.prod volume) := by
    refine Integrable.mono' (f.integrable.norm.mul_prod h.integrable.norm)
      hcont.aestronglyMeasurable (Eventually.of_forall fun p => le_of_eq ?_)
    simp only [hΦ, uncurry_def, norm_mul, norm_exp_two_pi_I_mul, one_mul]
  calc ∫ x, f x * (𝓕⁻ h : 𝓢(ℝ, ℂ)) (x * z) = ∫ x, ∫ w, Φ x w := by
        congr 1
        funext x
        simp only [hΦ]
        rw [fourierInv_apply_real, integral_const_mul]
    _ = ∫ w, ∫ x, Φ x w := integral_integral_swap hint
    _ = _ := by
        congr 1
        funext w
        simp only [hΦ]
        rw [fourierInv_apply_real, ← integral_const_mul]
        congr 1
        funext x
        rw [show w * (x * z) = x * (w * z) by ring]
        ring

/-- **Tate's identity** on the critical strip `0 < Re u < 1`:
`Z(f, e, u) Z(ĥ, e, 1 - u) = Z(f̂, e, 1 - u) Z(h, e, u)` with `^ = 𝓕⁻`. -/
theorem tate_identity (f h : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    zeta f e u * zeta (𝓕⁻ h : 𝓢(ℝ, ℂ)) e (1 - u) =
      zeta (𝓕⁻ f : 𝓢(ℝ, ℂ)) e (1 - u) * zeta h e u := by
  rw [zeta_mul_zeta_eq_integral f (𝓕⁻ h) e hu0 hu1, mul_comm (zeta _ e (1 - u)),
    zeta_mul_zeta_eq_integral h (𝓕⁻ f) e hu0 hu1]
  congr 1
  funext z
  rw [integral_mul_fourierInv_mul f h z]

end Langlands.LocalFactor.RealTate
