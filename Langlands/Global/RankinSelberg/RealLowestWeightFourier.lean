import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # Fourier inversion for the real lowest-weight Jacquet integral -/

noncomputable section

open Complex Filter MeasureTheory Set
open scoped FourierTransform Topology

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealLowestWeightFourier

private theorem integrableOn_pow_mul_cexp (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ n * exp (-z * x)) (Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => x ^ n * Real.exp (-x)) (Ioi 0) := by
    have hG := Real.GammaIntegral_convergent (show 0 < (n : ℝ) + 1 by positivity)
    simpa only [add_sub_cancel_right, Real.rpow_natCast, mul_comm] using hG
  have hScale : IntegrableOn (fun x : ℝ => (z.re * x) ^ n * Real.exp (-(z.re * x))) (Ioi 0) :=
    (integrableOn_Ioi_comp_mul_left_iff (fun x : ℝ => x ^ n * Real.exp (-x)) 0 hz).mpr (by simpa using h)
  have hBound : IntegrableOn (fun x : ℝ => (z.re ^ n)⁻¹ * ((z.re * x) ^ n * Real.exp (-(z.re * x)))) (Ioi 0) :=
    hScale.const_mul _
  apply (integrable_norm_iff (by fun_prop)).mp
  apply hBound.congr_fun _ measurableSet_Ioi
  intro x hx
  change 0 < x at hx
  simp only [norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hx, norm_exp,
    neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, mul_pow]
  field_simp [hz.ne']

private theorem tendsto_pow_mul_cexp_zero (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ n * exp (-z * x)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have h := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (n : ℝ) z.re hz
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  simp only [Real.rpow_natCast, norm_mul, norm_pow, norm_real, Real.norm_eq_abs, abs_of_pos hx,
    norm_exp, neg_mul, neg_re, mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero]

private theorem integral_pow_mul_cexp (n : ℕ) {z : ℂ} (hz : 0 < z.re) :
    (∫ x : ℝ in Ioi 0, (x : ℂ) ^ n * exp (-z * x)) = (n.factorial : ℂ) / z ^ (n + 1) := by
  have hnz : z ≠ 0 := fun h => hz.ne' (congrArg Complex.re h)
  induction n with
  | zero =>
      have h := integral_exp_mul_complex_Ioi (a := -z) (by simpa using hz) (0 : ℝ)
      simpa using h
  | succ n ih =>
      let u (x : ℝ) := (x : ℂ) ^ (n + 1)
      let u' (x : ℝ) := (n + 1 : ℂ) * (x : ℂ) ^ n
      let v (x : ℝ) := exp (-z * x)
      let v' (x : ℝ) := -z * v x
      have hu (x : ℝ) : HasDerivAt u (u' x) x := by
        simpa only [u, u', Nat.cast_add, Nat.cast_one, add_tsub_cancel_right] using
          (hasDerivAt_pow (n + 1) (x : ℂ)).comp_ofReal
      have hv (x : ℝ) : HasDerivAt v (v' x) x := by
        simpa [v, v', mul_comm] using (((hasDerivAt_id x).ofReal_comp).const_mul (-z)).cexp
      have hu'v : IntegrableOn (u' * v) (Ioi 0) := by
        change Integrable (fun x : ℝ => ((n + 1 : ℂ) * (x : ℂ) ^ n) * exp (-z * x))
          (volume.restrict (Ioi 0))
        simpa only [mul_assoc] using (integrableOn_pow_mul_cexp n hz).const_mul (n + 1 : ℂ)
      have huv' : IntegrableOn (u * v') (Ioi 0) := by
        change Integrable (fun x : ℝ => (x : ℂ) ^ (n + 1) * (-z * exp (-z * x)))
          (volume.restrict (Ioi 0))
        simpa only [mul_left_comm] using
          (integrableOn_pow_mul_cexp (n + 1) hz).const_mul (-z)
      have h0 : Tendsto (u * v) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hc : Continuous (u * v) := by dsimp [u, v]; fun_prop
        have hval : (u * v) 0 = 0 := by simp [u, v, zero_pow (Nat.succ_ne_zero n)]
        have hc0 : ContinuousAt (u * v) (0 : ℝ) := hc.continuousAt
        simpa only [hval] using hc0.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
      have htop : Tendsto (u * v) atTop (𝓝 0) := tendsto_pow_mul_cexp_zero (n + 1) hz
      have hP := integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ)) (fun x _ => hu x)
        (fun x _ => hv x) huv' hu'v h0 htop
      have hLeft (x : ℝ) : u x * v' x = -z * ((x : ℂ) ^ (n + 1) * exp (-z * x)) := by
        dsimp only [u, v, v']
        ring
      have hRight (x : ℝ) : u' x * v x = (n + 1 : ℂ) * ((x : ℂ) ^ n * exp (-z * x)) :=
        mul_assoc _ _ _
      simp only [hLeft, hRight, integral_const_mul, sub_self, zero_sub, ih] at hP
      rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ' z (n + 1)]
      apply mul_left_cancel₀ (neg_ne_zero.mpr hnz)
      rw [hP]
      field_simp

/-- The function whose Fourier transform is a reciprocal power of a real shifted linear factor. -/
def positiveExpPower (a : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ)) ^ (n + 1) / (n.factorial : ℂ) *
    ((max x 0 : ℝ) : ℂ) ^ n * exp (-((2 * Real.pi * a * x : ℝ) : ℂ))

private theorem fourier_positiveExpPower (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : n ≠ 0) (y : ℝ) :
    𝓕 (positiveExpPower a n) y = ((a : ℂ) + (y : ℂ) * I)⁻¹ ^ (n + 1) := by
  let A : ℂ := (2 * (Real.pi : ℂ)) ^ (n + 1) / (n.factorial : ℂ)
  let z : ℂ := (2 * (Real.pi : ℂ)) * ((a : ℂ) + (y : ℂ) * I)
  have hz : 0 < z.re := by
    have he : z.re = 2 * Real.pi * a := by simp [z, mul_re, mul_im]
    rw [he]
    positivity
  have hp : (fun x : ℝ => exp (↑(-2 * Real.pi * x * y) * I) • positiveExpPower a n x) =
      (Ioi 0).indicator (fun x : ℝ => A * ((x : ℂ) ^ n * exp (-z * x))) := by
    funext x
    by_cases hx : 0 < x
    · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
      simp only [positiveExpPower, max_eq_left hx.le, smul_eq_mul]
      calc
        _ = A * ((x : ℂ) ^ n * exp ((↑(-2 * Real.pi * x * y) : ℂ) * I +
            -(↑(2 * Real.pi * a * x) : ℂ))) := by rw [exp_add]; dsimp [A]; ring
        _ = _ := by congr 3; push_cast; dsimp [z]; ring
    · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
      simp [positiveExpPower, max_eq_right (not_lt.mp hx), zero_pow hn]
  rw [Real.fourier_real_eq_integral_exp_smul, hp, integral_indicator measurableSet_Ioi,
    integral_const_mul, integral_pow_mul_cexp n hz]
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by exact_mod_cast (show (2 * Real.pi : ℝ) ≠ 0 by positivity)
  have hnfac : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero n)
  have hden : (a : ℂ) + (y : ℂ) * I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [mul_re] at hr
    exact ha.ne' hr
  dsimp only [A, z]
  simp only [mul_pow, inv_pow]
  field_simp [hπ, hnfac, hden]

private theorem integrable_positiveExpPower (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : n ≠ 0) :
    Integrable (positiveExpPower a n) := by
  let A : ℂ := (2 * (Real.pi : ℂ)) ^ (n + 1) / (n.factorial : ℂ)
  let z : ℂ := (2 * (Real.pi : ℂ)) * (a : ℂ)
  have hz : 0 < z.re := by
    have he : z.re = 2 * Real.pi * a := by simp [z, mul_re, mul_im]
    rw [he]
    positivity
  have h : Integrable ((Ioi 0).indicator (fun x : ℝ => A * ((x : ℂ) ^ n * exp (-z * x)))) :=
    (integrable_indicator_iff measurableSet_Ioi).mpr ((integrableOn_pow_mul_cexp n hz).const_mul A)
  apply h.congr (ae_of_all _ fun x => ?_)
  by_cases hx : 0 < x
  · rw [indicator_of_mem (show x ∈ Ioi (0 : ℝ) from hx)]
    simp only [positiveExpPower, max_eq_left hx.le, z, A, ofReal_mul, ofReal_ofNat, neg_mul, mul_assoc]
  · rw [indicator_of_notMem (show x ∉ Ioi (0 : ℝ) from hx)]
    simp [positiveExpPower, max_eq_right (not_lt.mp hx), zero_pow hn]

private theorem integrable_reciprocalPower (a : ℝ) (ha : 0 < a) (n : ℕ) (hn : n ≠ 0) :
    Integrable (fun y : ℝ => ((a : ℂ) + (y : ℂ) * I)⁻¹ ^ (n + 1)) := by
  have hBound := (integrable_inv_one_add_mul_sq (inv_ne_zero ha.ne')).const_mul (a⁻¹ ^ (n + 1))
  refine hBound.mono' (by fun_prop) (ae_of_all _ fun x => ?_)
  let r := ‖(a : ℂ) + (x : ℂ) * I‖
  have hr : 0 < r := by
    dsimp only [r]
    rw [Complex.norm_add_mul_I]
    positivity
  have hr2 : r ^ 2 = a ^ 2 + x ^ 2 := by
    dsimp only [r]
    rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]
  have hra : a ≤ r := by nlinarith [sq_nonneg x]
  have hn' : n + 1 = (n - 1) + 2 := by omega
  calc
    ‖((a : ℂ) + (x : ℂ) * I)⁻¹ ^ (n + 1)‖ = r⁻¹ ^ (n - 1) * (r ^ 2)⁻¹ := by
      rw [norm_pow, norm_inv]
      change r⁻¹ ^ (n + 1) = _
      simp only [hn', pow_add, inv_pow]
    _ ≤ a⁻¹ ^ (n - 1) * (a ^ 2 + x ^ 2)⁻¹ := by
      rw [hr2]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (inv_nonneg.mpr hr.le)
        (inv_anti₀ ha hra) _) (by positivity)
    _ = a⁻¹ ^ (n + 1) * (1 + (a⁻¹ * x) ^ 2)⁻¹ := by
      rw [hn', pow_add]
      field_simp

/-- The reciprocal powers in the open-cell integrals are integrable, and their
Fourier values are positive-half-line exponential powers. -/
def RealLowestWeightFourierStatement : Prop :=
  ∀ (a : ℝ), 0 < a → ∀ (n : ℕ), n ≠ 0 →
    let f := fun x : ℝ => ((a : ℂ) - (x : ℂ) * I)⁻¹ ^ (n + 1)
    Integrable f ∧ 𝓕 f = positiveExpPower a n

theorem realLowestWeightFourier : RealLowestWeightFourierStatement := by
  intro a ha n hn f
  have hFourier := funext (fourier_positiveExpPower a ha n hn)
  have hInv : 𝓕⁻ (positiveExpPower a n) = f := by
    funext x
    rw [Real.fourierInv_eq_fourier_neg, hFourier]
    simp [f, sub_eq_add_neg]
  have hi : Integrable f := by
    have h := (integrable_reciprocalPower a ha n hn).comp_neg
    simpa [f, sub_eq_add_neg] using h
  refine ⟨hi, ?_⟩
  have hC : Continuous (positiveExpPower a n) := by unfold positiveExpPower; fun_prop
  have hF : Integrable (𝓕 (positiveExpPower a n)) := hFourier.symm ▸ integrable_reciprocalPower a ha n hn
  have he := hC.fourier_fourierInv_eq (integrable_positiveExpPower a ha n hn) hF
  rwa [hInv] at he

end Langlands.Global.RankinSelbergGlobal.RealLowestWeightFourier
