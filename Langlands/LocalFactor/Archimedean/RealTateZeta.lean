import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Real Tate zeta integrals: convergence and holomorphy

For a Schwartz function `f` on `ℝ`, a parity `e ∈ {0, 1}` and `u ∈ ℂ`, the real Tate zeta
integral is `Z(f, e, u) = ∫ f(x) sgn(x)^e |x|^(u-1) dx` (Lebesgue measure), with the integrand
set to `0` at `x = 0`. For `0 < Re u` it is the sum of two Mellin transforms, of `f` and of
`x ↦ f(-x)`; this gives absolute convergence and holomorphy on that half-plane. We also record
the behaviour under scalar multiples and dilations. See the paired Markdown.
-/

noncomputable section

open MeasureTheory Filter Set Asymptotics
open scoped SchwartzMap Topology

namespace Langlands.LocalFactor.RealTate

/-- The integrand `f(x) sgn(x)^e |x|^(u-1)` of the real Tate zeta integral, set to `0` at
`x = 0`. -/
def integrand (f : ℝ → ℂ) (e : Fin 2) (u : ℂ) (x : ℝ) : ℂ :=
  if x = 0 then 0 else f x * ((x / |x| : ℝ) : ℂ) ^ e.val * ((|x| : ℝ) : ℂ) ^ (u - 1)

/-- The real Tate zeta integral `∫ f(x) sgn(x)^e |x|^(u-1) dx`. -/
def zeta (f : ℝ → ℂ) (e : Fin 2) (u : ℂ) : ℂ :=
  ∫ x, integrand f e u x

/-- The reflection `x ↦ f(-x)` of a Schwartz function. -/
def reflect (f : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
    (LinearIsometryEquiv.neg ℝ (E := ℝ)).toContinuousLinearEquiv f

@[simp]
theorem reflect_apply (f : 𝓢(ℝ, ℂ)) (x : ℝ) : reflect f x = f (-x) := rfl

theorem sign_sq_eq_one {x : ℝ} (hx : x ≠ 0) : ((x / |x| : ℝ) : ℂ) ^ 2 = 1 := by
  have h : (x / |x|) ^ 2 = 1 := by
    rw [div_pow, sq_abs, div_self (pow_ne_zero 2 hx)]
  exact_mod_cast h

theorem sign_pow_mul_self {x : ℝ} (hx : x ≠ 0) (e : Fin 2) :
    ((x / |x| : ℝ) : ℂ) ^ e.val * ((x / |x| : ℝ) : ℂ) ^ e.val = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, sign_sq_eq_one hx, one_pow]

theorem sign_mul (x y : ℝ) :
    (((x * y) / |x * y| : ℝ) : ℂ) = ((x / |x| : ℝ) : ℂ) * ((y / |y| : ℝ) : ℂ) := by
  rw [abs_mul, mul_div_mul_comm]
  push_cast
  ring

theorem integrand_zero (f : ℝ → ℂ) (e : Fin 2) (u : ℂ) : integrand f e u 0 = 0 := by
  simp [integrand]

theorem integrand_of_pos (f : ℝ → ℂ) (e : Fin 2) (u : ℂ) {x : ℝ} (hx : 0 < x) :
    integrand f e u x = (x : ℂ) ^ (u - 1) • f x := by
  simp only [integrand, ne_of_gt hx, ↓reduceIte]
  rw [abs_of_pos hx, div_self hx.ne', smul_eq_mul]
  simp [mul_comm]

theorem integrand_of_neg (f : ℝ → ℂ) (e : Fin 2) (u : ℂ) {x : ℝ} (hx : x < 0) :
    integrand f e u x = (-1 : ℂ) ^ e.val * (((-x : ℝ) : ℂ) ^ (u - 1) • f (-(-x))) := by
  simp only [integrand, ne_of_lt hx, ↓reduceIte]
  rw [abs_of_neg hx, neg_neg, smul_eq_mul]
  have h : x / -x = -1 := by
    rw [div_neg, div_self hx.ne]
  rw [h]
  push_cast
  ring

theorem integrand_const_mul (c : ℂ) (f : ℝ → ℂ) (e : Fin 2) (u : ℂ) (x : ℝ) :
    integrand (fun y => c * f y) e u x = c * integrand f e u x := by
  unfold integrand
  split_ifs <;> ring

theorem zeta_const_mul (c : ℂ) (f : ℝ → ℂ) (e : Fin 2) (u : ℂ) :
    zeta (fun y => c * f y) e u = c * zeta f e u := by
  simp only [zeta, integrand_const_mul, integral_const_mul]

theorem measurable_integrand {f : ℝ → ℂ} (hf : Measurable f) (e : Fin 2) (u : ℂ) :
    Measurable (integrand f e u) := by
  unfold integrand
  refine Measurable.ite (measurableSet_singleton 0) measurable_const ?_
  fun_prop

/-! ### Decay of Schwartz functions -/

theorem isBigO_atTop (f : 𝓢(ℝ, ℂ)) (a : ℝ) :
    (fun x : ℝ => f x) =O[atTop] (· ^ (-a)) := by
  have h := (f.isBigO_cocompact_rpow (-a)).mono atTop_le_cocompact
  refine h.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_gt_atTop 0] with x hx
  rw [Real.norm_of_nonneg hx.le]

theorem isBigO_nhdsGT (f : 𝓢(ℝ, ℂ)) :
    (fun x : ℝ => f x) =O[𝓝[>] 0] (· ^ (-(0 : ℝ))) := by
  have h : (fun x : ℝ => f x) =O[𝓝[>] 0] (fun _ => (1 : ℝ)) :=
    (f.continuous.tendsto 0).mono_left nhdsWithin_le_nhds |>.isBigO_one ℝ
  refine h.congr' EventuallyEq.rfl ?_
  filter_upwards with x
  simp

theorem mellinConvergent (f : 𝓢(ℝ, ℂ)) {u : ℂ} (hu : 0 < u.re) :
    MellinConvergent (fun x => f x) u :=
  mellinConvergent_of_isBigO_rpow (f.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (isBigO_atTop f (u.re + 1)) (by linarith) (isBigO_nhdsGT f) (by simpa using hu)

theorem differentiableAt_mellin (f : 𝓢(ℝ, ℂ)) {u : ℂ} (hu : 0 < u.re) :
    DifferentiableAt ℂ (mellin (fun x => f x)) u :=
  mellin_differentiableAt_of_isBigO_rpow
    (f.continuous.continuousOn.locallyIntegrableOn measurableSet_Ioi)
    (isBigO_atTop f (u.re + 1)) (by linarith) (isBigO_nhdsGT f) (by simpa using hu)

/-! ### Convergence and the Mellin decomposition -/

theorem integrableOn_Ioi (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu : 0 < u.re) :
    IntegrableOn (integrand f e u) (Ioi 0) :=
  (mellinConvergent f hu).congr_fun (fun _ hx => (integrand_of_pos f e u hx).symm)
    measurableSet_Ioi

theorem integrableOn_Iio (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu : 0 < u.re) :
    IntegrableOn (integrand f e u) (Iio 0) := by
  have h0 : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (u - 1) • reflect f t) (Ioi (-0)) := by
    rw [neg_zero]
    exact mellinConvergent (reflect f) hu
  have h1 := IntegrableOn.comp_neg_Iio (c := (0 : ℝ)) h0
  have h2 : IntegrableOn (fun x : ℝ => (-1 : ℂ) ^ e.val *
      (((-x : ℝ) : ℂ) ^ (u - 1) • reflect f (-x))) (Iio 0) :=
    h1.const_mul ((-1 : ℂ) ^ e.val)
  refine h2.congr_fun (fun x hx => ?_) measurableSet_Iio
  rw [integrand_of_neg f e u hx]
  simp

theorem integrable_integrand (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu : 0 < u.re) :
    Integrable (integrand f e u) := by
  have h2 : IntegrableOn (integrand f e u) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by simp [integrand_zero])).mpr
      (integrableOn_Ioi f e hu)
  have := (integrableOn_Iio f e hu).union h2
  rwa [Iio_union_Ici, integrableOn_univ] at this

theorem zeta_eq_mellin (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu : 0 < u.re) :
    zeta f e u = mellin (fun x => f x) u + (-1 : ℂ) ^ e.val * mellin (fun x => reflect f x) u := by
  have h2 : IntegrableOn (integrand f e u) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by simp [integrand_zero])).mpr
      (integrableOn_Ioi f e hu)
  rw [zeta, ← intervalIntegral.integral_Iio_add_Ici (integrableOn_Iio f e hu) h2, integral_Ici_eq_integral_Ioi,
    add_comm]
  congr 1
  · exact setIntegral_congr_fun measurableSet_Ioi (fun x hx => integrand_of_pos f e u hx)
  · have h1 : ∫ x in Iio 0, integrand f e u x =
        ∫ x in Iio 0, (-1 : ℂ) ^ e.val * (((-x : ℝ) : ℂ) ^ (u - 1) • reflect f (-x)) :=
      setIntegral_congr_fun measurableSet_Iio (fun x hx => by
        rw [integrand_of_neg f e u hx]; simp)
    rw [h1, integral_const_mul, mellin, ← integral_Iic_eq_integral_Iio]
    congr 1
    have := integral_comp_neg_Ioi (0 : ℝ)
      (fun x : ℝ => ((-x : ℝ) : ℂ) ^ (u - 1) • reflect f (-x))
    simp only [neg_neg, neg_zero] at this
    rw [← this]

theorem differentiableAt_zeta (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu : 0 < u.re) :
    DifferentiableAt ℂ (zeta f e) u := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : (fun w => mellin (fun x => f x) w + (-1 : ℂ) ^ e.val *
      mellin (fun x => reflect f x) w) =ᶠ[𝓝 u] zeta f e := by
    filter_upwards [hopen.mem_nhds hu] with w hw
    exact (zeta_eq_mellin f e hw).symm
  exact ((differentiableAt_mellin f hu).add
    ((differentiableAt_mellin (reflect f) hu).const_mul _)).congr_of_eventuallyEq hev.symm

theorem differentiableOn_zeta (f : 𝓢(ℝ, ℂ)) (e : Fin 2) :
    DifferentiableOn ℂ (zeta f e) {u : ℂ | 0 < u.re} :=
  fun _ hu => (differentiableAt_zeta f e hu).differentiableWithinAt

theorem analyticAt_zeta (f : 𝓢(ℝ, ℂ)) (e : Fin 2) {u : ℂ} (hu : 0 < u.re) :
    AnalyticAt ℂ (zeta f e) u := by
  have hopen : IsOpen {w : ℂ | 0 < w.re} := isOpen_lt continuous_const Complex.continuous_re
  exact DifferentiableOn.analyticAt (differentiableOn_zeta f e) (hopen.mem_nhds hu)

/-! ### Dilations -/

theorem abs_cpow_ne_zero {a : ℝ} (ha : a ≠ 0) : ((|a| : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (abs_ne_zero.mpr ha)

theorem integrand_mul (φ : ℝ → ℂ) (e : Fin 2) (w : ℂ) {a : ℝ} (ha : a ≠ 0) (x : ℝ) :
    integrand φ e w (a * x) = ((a / |a| : ℝ) : ℂ) ^ e.val * ((|a| : ℝ) : ℂ) ^ (w - 1) *
      integrand (fun y => φ (a * y)) e w x := by
  by_cases hx : x = 0
  · simp [hx, integrand_zero]
  · have hax : a * x ≠ 0 := mul_ne_zero ha hx
    simp only [integrand, hax, hx, ↓reduceIte]
    rw [sign_mul, abs_mul, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (abs_nonneg a) (abs_nonneg x), mul_pow]
    ring

theorem sign_pow_mul_sign_pow {a : ℝ} (ha : a ≠ 0) (e : Fin 2) :
    ((a / |a| : ℝ) : ℂ) ^ e.val * ((a / |a| : ℝ) : ℂ) ^ e.val = 1 :=
  sign_pow_mul_self ha e

/-- Dilation: `Z(φ, e, w) = sgn(a)^e |a|^w Z(φ(a ·), e, w)`. -/
theorem zeta_eq_sign_mul_zeta_comp_mul (φ : ℝ → ℂ) (e : Fin 2) (w : ℂ) {a : ℝ} (ha : a ≠ 0) :
    zeta φ e w = ((a / |a| : ℝ) : ℂ) ^ e.val * ((|a| : ℝ) : ℂ) ^ w *
      zeta (fun y => φ (a * y)) e w := by
  have h := Measure.integral_comp_mul_left (integrand φ e w) a
  simp only [integrand_mul φ e w ha, integral_const_mul] at h
  have hA := abs_cpow_ne_zero ha
  rw [abs_inv, Complex.real_smul, Complex.ofReal_inv] at h
  have h1 : ((|a| : ℝ) : ℂ) ^ w = ((|a| : ℝ) : ℂ) * ((|a| : ℝ) : ℂ) ^ (w - 1) := by
    conv_lhs => rw [show w = 1 + (w - 1) by ring]
    rw [Complex.cpow_add _ _ hA, Complex.cpow_one]
  unfold zeta
  rw [h1]
  calc ∫ x, integrand φ e w x
      = ((|a| : ℝ) : ℂ) * (((|a| : ℝ) : ℂ)⁻¹ * ∫ x, integrand φ e w x) := by
        rw [← mul_assoc, mul_inv_cancel₀ hA, one_mul]
    _ = _ := by rw [← h]; ring

end Langlands.LocalFactor.RealTate
