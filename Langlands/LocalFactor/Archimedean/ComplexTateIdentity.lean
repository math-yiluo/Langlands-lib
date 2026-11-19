import Langlands.LocalFactor.Archimedean.ComplexTateZeta
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.RingTheory.Complex

/-! # The complex trace Fourier transform and Tate's integral identity -/

noncomputable section

open Complex MeasureTheory Filter Function
open scoped SchwartzMap FourierTransform ENNReal Real

namespace Langlands.LocalFactor.ComplexTate

local instance : Measure.IsAddHaarMeasure measure :=
  Measure.IsAddHaarMeasure.smul volume (by simp) (by simp)

private def mulCLE (a : ℂˣ) : ℂ ≃L[ℝ] ℂ :=
  (ContinuousLinearEquiv.unitsEquivAut ℂ a).restrictScalars ℝ

@[simp] private theorem mulCLE_apply (a : ℂˣ) (x : ℂ) : mulCLE a x = (a : ℂ) * x := by
  change x * (a : ℂ) = (a : ℂ) * x
  exact mul_comm _ _

private def mulEquiv (a : ℂˣ) : ℂ ≃ᵐ ℂ :=
  (mulCLE a).toHomeomorph.toMeasurableEquiv

private theorem mulEquiv_apply (a : ℂˣ) (x : ℂ) : mulEquiv a x = (a : ℂ) * x :=
  mulCLE_apply a x

private theorem jacobian_pos (a : ℂˣ) : 0 < ‖(a : ℂ)‖ ^ 2 :=
  pow_pos (norm_pos_iff.mpr (Units.ne_zero a)) 2

private theorem map_mulEquiv (a : ℂˣ) :
    Measure.map (mulEquiv a) measure = ENNReal.ofReal (‖(a : ℂ)‖ ^ 2)⁻¹ • measure := by
  let L := (mulCLE a).toLinearEquiv.toLinearMap
  have hL : L = Algebra.lmul ℝ ℂ (a : ℂ) := by
    ext x
    exact mulCLE_apply a x
  have hdet : L.det = ‖(a : ℂ)‖ ^ 2 := by
    rw [hL, ← Algebra.norm_apply, Algebra.norm_complex_apply, Complex.sq_norm]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar measure
    (f := L) (hdet.trans_ne (jacobian_pos a).ne')
  rw [hdet, abs_of_pos (inv_pos.mpr (jacobian_pos a))] at h
  exact h

private theorem integral_comp_mul_left {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℂˣ) (g : ℂ → E) :
    ∫ x, g ((a : ℂ) * x) ∂measure = (‖(a : ℂ)‖ ^ 2)⁻¹ • ∫ x, g x ∂measure := by
  simpa only [map_mulEquiv, integral_smul_measure, mulEquiv_apply,
    ENNReal.toReal_ofReal (inv_nonneg.mpr (jacobian_pos a).le)] using
    (integral_map_equiv (μ := measure) (mulEquiv a) g).symm

private theorem integrable_comp_mul_left {E : Type*} [NormedAddCommGroup E]
    (a : ℂˣ) {g : ℂ → E} (hg : Integrable g measure) :
    Integrable (fun x => g ((a : ℂ) * x)) measure := by
  have hg' : Integrable g (Measure.map (mulEquiv a) measure) := by
    rw [map_mulEquiv]
    exact hg.smul_measure ENNReal.ofReal_ne_top
  rw [← show g ∘ mulEquiv a = (fun x => g ((a : ℂ) * x)) from
    funext fun x => congrArg g (mulEquiv_apply a x)]
  exact (integrable_map_equiv (mulEquiv a) g).mp hg'

private theorem integrand_mul_arg (f : ℂ → ℂ) (m : ℤ) (u : ℂ) {a : ℂ} (ha : a ≠ 0)
    (z : ℂ) :
    integrand f m u (a * z) =
      direction a ^ m * (‖a‖ : ℂ) ^ (2 * u - 2) *
        integrand (fun w => f (a * w)) m u z := by
  by_cases hz : z = 0
  · simp [hz, integrand]
  simp only [integrand, hz, mul_ne_zero ha hz, ite_false]
  rw [direction_mul, mul_zpow, norm_mul, ofReal_mul,
    mul_cpow_ofReal_nonneg (norm_nonneg _) (norm_nonneg _)]
  ring

theorem zeta_dilate (a : ℂˣ) (f : ℂ → ℂ) (m : ℤ) (u : ℂ) :
    zeta (fun z => f ((a : ℂ) * z)) m u =
      direction (a : ℂ) ^ (-m) * (‖(a : ℂ)‖ : ℂ) ^ (-2 * u) * zeta f m u := by
  have ha : (a : ℂ) ≠ 0 := Units.ne_zero a
  have hn : (‖(a : ℂ)‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr ha)
  have hd := zpow_ne_zero m (direction_ne_zero ha)
  have h (z : ℂ) : integrand (fun w => f ((a : ℂ) * w)) m u z =
      (direction (a : ℂ) ^ (-m) * (‖(a : ℂ)‖ : ℂ) ^ (-(2 * u - 2))) *
        integrand f m u ((a : ℂ) * z) := by
    rw [integrand_mul_arg f m u ha, zpow_neg, cpow_neg]
    have hp : (‖(a : ℂ)‖ : ℂ) ^ (2 * u - 2) ≠ 0 := cpow_ne_zero_iff.mpr (Or.inl hn)
    field_simp
  have hp : (‖(a : ℂ)‖ : ℂ) ^ (-(2 * u - 2)) * ((‖(a : ℂ)‖ : ℂ) ^ 2)⁻¹ =
      (‖(a : ℂ)‖ : ℂ) ^ (-2 * u) := by
    have htwo : (‖(a : ℂ)‖ : ℂ) ^ (2 : ℂ) = (‖(a : ℂ)‖ : ℂ) ^ (2 : ℕ) := by
      exact mod_cast cpow_natCast (‖(a : ℂ)‖ : ℂ) 2
    rw [← htwo, ← cpow_neg, ← cpow_add _ _ hn]
    congr 1
    ring
  simp only [zeta, h]
  rw [integral_const_mul, integral_comp_mul_left, Complex.real_smul, ofReal_inv, ofReal_pow]
  rw [mul_assoc, ← mul_assoc ((‖(a : ℂ)‖ : ℂ) ^ (-(2 * u - 2))), hp, ← mul_assoc]

/-- The positive character of the complex trace pairing evaluated at a product. -/
def traceChar (z : ℂ) : ℂ := Complex.exp (4 * (Real.pi : ℂ) * I * (z.re : ℂ))

private theorem norm_traceChar (z : ℂ) : ‖traceChar z‖ = 1 := by
  rw [traceChar, show 4 * (Real.pi : ℂ) * I * (z.re : ℂ) =
    ((4 * Real.pi * z.re : ℝ) : ℂ) * I by push_cast; ring]
  exact norm_exp_ofReal_mul_I _

/-- The positive trace Fourier transform, with twice area as the integration measure. -/
def fourier (f : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  (2 : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    ((mulCLE (Units.mk0 2 (by norm_num))).trans conjCLE) (𝓕⁻ f)

theorem fourier_apply (f : 𝓢(ℂ, ℂ)) (y : ℂ) :
    fourier f y = ∫ x, traceChar (x * y) * f x ∂measure := by
  have hinner (x : ℂ) : inner ℝ x (starRingEnd ℂ (2 * y)) = 2 * (x * y).re := by
    rw [Complex.inner, ← map_mul, conj_re, show 2 * y * x = 2 * (x * y) by ring]
    simp [mul_re]
  simp only [fourier, smul_apply, smul_eq_mul,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, comp_apply,
    ContinuousLinearEquiv.trans_apply, mulCLE_apply, Units.val_mk0, conjCLE_apply,
    SchwartzMap.fourierInv_coe, Real.fourierInv_eq', measure, integral_smul_measure,
    ENNReal.toReal_ofNat, Complex.real_smul, ofReal_ofNat, traceChar, hinner]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  dsimp only
  rw [show ((2 * Real.pi * (2 * (x * y).re) : ℝ) : ℂ) * I =
    4 * (Real.pi : ℂ) * I * ((x * y).re : ℂ) by push_cast; ring]

/-- The trace Fourier transform with scaled additive character and Haar measure. -/
def scaledFourier (a : ℂˣ) (c : NNReal) (f : 𝓢(ℂ, ℂ)) : 𝓢(ℂ, ℂ) :=
  (c : ℂ) • SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulCLE a) (fourier f)

theorem scaledFourier_apply (a : ℂˣ) (c : NNReal) (f : 𝓢(ℂ, ℂ)) (y : ℂ) :
    scaledFourier a c f y = (c : ℂ) * ∫ x, traceChar ((a : ℂ) * x * y) * f x ∂measure := by
  simp only [scaledFourier, smul_apply, smul_eq_mul,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, comp_apply, mulCLE_apply, fourier_apply]
  simp only [mul_left_comm _ (a : ℂ), mul_assoc]

theorem zeta_scaledFourier (a : ℂˣ) (c : NNReal) (f : 𝓢(ℂ, ℂ)) (m : ℤ) (u : ℂ) :
    zeta (scaledFourier a c f) m u =
      (c : ℂ) * direction (a : ℂ) ^ (-m) * (‖(a : ℂ)‖ : ℂ) ^ (-2 * u) *
        zeta (fourier f) m u := by
  have h : (scaledFourier a c f : ℂ → ℂ) = fun x => (c : ℂ) * fourier f ((a : ℂ) * x) := by
    funext x
    simp only [scaledFourier, smul_apply, smul_eq_mul,
      SchwartzMap.compCLMOfContinuousLinearEquiv_apply, comp_apply, mulCLE_apply]
  simp only [h, zeta_const_mul, zeta_dilate, mul_assoc]

/-! ## The common-strip identity -/

private def kernel (m : ℤ) (u : ℂ) (z : ℂ) : ℂ :=
  integrand (fun _ => 1) (-m) (1 - u) z

private theorem ae_ne_zero : ∀ᵐ z ∂measure, z ≠ (0 : ℂ) := by
  rw [ae_iff]
  simp [measure]

private theorem integrand_mul_jacobian (f φ : ℂ → ℂ) (m : ℤ) (u : ℂ) {x : ℂ} (hx : x ≠ 0)
    (z : ℂ) :
    integrand f m u x *
      (((‖x‖ ^ 2 : ℝ) : ℂ) * integrand φ (-m) (1 - u) (x * z)) =
        f x * φ (x * z) * kernel m u z := by
  by_cases hz : z = 0
  · simp [hz, integrand, kernel]
  have hn : (‖x‖ : ℂ) ≠ 0 := ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hx)
  have hdir : direction x ^ m * direction x ^ (-m) = 1 := by
    rw [zpow_neg, mul_inv_cancel₀ (zpow_ne_zero _ (direction_ne_zero hx))]
  have hrad : (‖x‖ : ℂ) ^ (2 * u - 2) * (‖x‖ : ℂ) ^ (2 * (1 - u) - 2) *
      (‖x‖ : ℂ) ^ 2 = 1 := by
    have htwo : (‖x‖ : ℂ) ^ (2 : ℂ) = (‖x‖ : ℂ) ^ (2 : ℕ) := by
      exact mod_cast cpow_natCast (‖x‖ : ℂ) 2
    rw [← cpow_add _ _ hn, show 2 * u - 2 + (2 * (1 - u) - 2) = -(2 : ℂ) by ring,
      cpow_neg, htwo, inv_mul_cancel₀ (pow_ne_zero _ hn)]
  rw [integrand_mul_arg φ (-m) (1 - u) hx z]
  simp only [integrand, kernel, hx, hz, ite_false, one_mul, ofReal_pow]
  calc
    _ = (direction x ^ m * direction x ^ (-m)) *
        ((‖x‖ : ℂ) ^ (2 * u - 2) * (‖x‖ : ℂ) ^ (2 * (1 - u) - 2) * (‖x‖ : ℂ) ^ 2) *
        (f x * φ (x * z) * (direction z ^ (-m) * (‖z‖ : ℂ) ^ (2 * (1 - u) - 2))) := by ring
    _ = _ := by rw [hdir, hrad, one_mul, one_mul]

private theorem integrable_slice (f φ : ℂ → ℂ) (m : ℤ) (u : ℂ)
    (hφ : Integrable (integrand φ (-m) (1 - u)) measure) {x : ℂ} (hx : x ≠ 0) :
    Integrable (fun z => f x * φ (x * z) * kernel m u z) measure := by
  simp_rw [← integrand_mul_jacobian f φ m u hx]
  exact ((integrable_comp_mul_left (Units.mk0 x hx) hφ).const_mul _).const_mul _

private theorem integral_slice (f φ : ℂ → ℂ) (m : ℤ) (u : ℂ) {x : ℂ} (hx : x ≠ 0) :
    ∫ z, f x * φ (x * z) * kernel m u z ∂measure = integrand f m u x * zeta φ (-m) (1 - u) := by
  have h := integral_comp_mul_left (Units.mk0 x hx) (integrand φ (-m) (1 - u))
  simp only [Units.val_mk0, Complex.real_smul] at h
  simp_rw [← integrand_mul_jacobian f φ m u hx]
  rw [integral_const_mul, integral_const_mul, h]
  rw [← mul_assoc ((‖x‖ ^ 2 : ℝ) : ℂ), ← ofReal_mul,
    mul_inv_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hx)), ofReal_one, one_mul, zeta]

private theorem integral_norm_slice (f φ : ℂ → ℂ) (m : ℤ) (u : ℂ) {x : ℂ} (hx : x ≠ 0) :
    ∫ z, ‖f x * φ (x * z) * kernel m u z‖ ∂measure =
      ‖integrand f m u x‖ * ∫ y, ‖integrand φ (-m) (1 - u) y‖ ∂measure := by
  have h := integral_comp_mul_left (Units.mk0 x hx) (fun y => ‖integrand φ (-m) (1 - u) y‖)
  simp only [Units.val_mk0, smul_eq_mul] at h
  simp_rw [← integrand_mul_jacobian f φ m u hx, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_nonneg (sq_nonneg ‖x‖)]
  rw [integral_const_mul, integral_const_mul, h]
  rw [← mul_assoc (‖x‖ ^ 2), mul_inv_cancel₀ (pow_ne_zero _ (norm_ne_zero_iff.mpr hx)), one_mul]

private theorem zeta_mul_zeta_eq_integral (f φ : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ} (hu0 : 0 < u.re)
    (hu1 : u.re < 1) :
    zeta f m u * zeta φ (-m) (1 - u) =
      ∫ z, (∫ x, f x * φ (x * z) ∂measure) * kernel m u z ∂measure := by
  have hf := integrable_integrand f m hu0
  have hφ : Integrable (integrand φ (-m) (1 - u)) measure :=
    integrable_integrand φ (-m) (by simpa [sub_re] using sub_pos.mpr hu1)
  let F (x z : ℂ) := f x * φ (x * z) * kernel m u z
  have hmeas : AEStronglyMeasurable (uncurry F) (measure.prod measure) := by
    refine Measurable.aestronglyMeasurable ?_
    exact ((f.continuous.measurable.comp measurable_fst).mul
      (φ.continuous.measurable.comp (measurable_fst.mul measurable_snd))).mul
      ((measurable_integrand measurable_const (-m) (1 - u)).comp measurable_snd)
  have hint : Integrable (uncurry F) (measure.prod measure) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨ae_ne_zero.mono (fun x hx => integrable_slice f φ m u hφ hx), ?_⟩
    refine (hf.norm.mul_const (∫ y, ‖integrand φ (-m) (1 - u) y‖ ∂measure)).congr ?_
    exact ae_ne_zero.mono fun x hx => (integral_norm_slice f φ m u hx).symm
  calc
    zeta f m u * zeta φ (-m) (1 - u) = ∫ x, (∫ z, F x z ∂measure) ∂measure := by
      rw [zeta, ← integral_mul_const]
      exact integral_congr_ae (ae_ne_zero.mono fun x hx => (integral_slice f φ m u hx).symm)
    _ = ∫ z, (∫ x, F x z ∂measure) ∂measure := integral_integral_swap hint
    _ = _ := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      exact integral_mul_const _ _

private theorem integral_mul_fourier_mul (f h : 𝓢(ℂ, ℂ)) (z : ℂ) :
    ∫ x, f x * fourier h (x * z) ∂measure = ∫ w, h w * fourier f (w * z) ∂measure := by
  let F (x w : ℂ) := f x * (traceChar (w * (x * z)) * h w)
  have hcont : Continuous (uncurry F) := by
    simp only [F, uncurry_def, traceChar]
    fun_prop
  have hf : Integrable f measure := f.integrable.smul_measure (by simp)
  have hh : Integrable h measure := h.integrable.smul_measure (by simp)
  have hint : Integrable (uncurry F) (measure.prod measure) := by
    refine Integrable.mono' (hf.norm.mul_prod hh.norm)
      hcont.aestronglyMeasurable (Eventually.of_forall fun p => le_of_eq ?_)
    simp only [F, uncurry_def, norm_mul, norm_traceChar, one_mul]
  calc
    ∫ x, f x * fourier h (x * z) ∂measure = ∫ x, (∫ w, F x w ∂measure) ∂measure := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [F, fourier_apply, integral_const_mul]
    _ = ∫ w, (∫ x, F x w ∂measure) ∂measure := integral_integral_swap hint
    _ = _ := by
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      dsimp only
      rw [fourier_apply, ← integral_const_mul]
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [F, show w * (x * z) = x * (w * z) by ring]
      ring

/-- The cross-multiplied identity for two Schwartz functions on `0 < Re u < 1`. -/
theorem tate_identity (f h : 𝓢(ℂ, ℂ)) (m : ℤ) {u : ℂ} (hu0 : 0 < u.re) (hu1 : u.re < 1) :
    zeta f m u * zeta (fourier h) (-m) (1 - u) =
      zeta (fourier f) (-m) (1 - u) * zeta h m u := by
  rw [zeta_mul_zeta_eq_integral f (fourier h) m hu0 hu1,
    mul_comm (zeta (fourier f) (-m) (1 - u)),
    zeta_mul_zeta_eq_integral h (fourier f) m hu0 hu1]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [integral_mul_fourier_mul f h z]

end Langlands.LocalFactor.ComplexTate
