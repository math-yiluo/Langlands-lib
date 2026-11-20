import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.MellinTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Integration by parts for the Mellin transform of a Schwartz function -/

noncomputable section

open MeasureTheory Filter Set Asymptotics
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

private theorem schwartz_isBigO_one (f : SchwartzMap ℝ ℂ) (l : Filter ℝ) :
    (f : ℝ → ℂ) =O[l] (fun _ => (1 : ℝ)) := by
  refine IsBigO.of_bound (SchwartzMap.seminorm ℝ 0 0 f) (Eventually.of_forall fun x => ?_)
  simpa only [norm_one, mul_one] using SchwartzMap.norm_le_seminorm ℝ f x

private theorem schwartz_isBigO_atTop_rpow (f : SchwartzMap ℝ ℂ) (s : ℝ) :
    (f : ℝ → ℂ) =O[atTop] (fun x : ℝ => x ^ s) := by
  refine ((f.isBigO_cocompact_rpow s).mono atTop_le_cocompact).congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  rw [Real.norm_of_nonneg hx]

/-- A Schwartz function of a real radius has a convergent Mellin integral
on the positive half-plane. -/
theorem schwartz_mellinConvergent (f : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent f s := by
  refine mellinConvergent_of_isBigO_rpow (a := s.re + 1) (b := 0)
    (f.continuous.locallyIntegrable.locallyIntegrableOn (Ioi 0))
    (schwartz_isBigO_atTop_rpow f _) (by linarith) ?_ hs
  simpa using schwartz_isBigO_one f (𝓝[>] (0 : ℝ))

private theorem ofReal_cpow_isBigO_rpow (l : Filter ℝ) (hl : ∀ᶠ x in l, 0 < x) (s : ℂ) :
    (fun x : ℝ => (x : ℂ) ^ s) =O[l] (fun x : ℝ => x ^ s.re) := by
  refine IsBigO.of_bound 1 (hl.mono fun x hx => ?_)
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, Real.norm_of_nonneg (Real.rpow_nonneg hx.le _),
    one_mul]

private theorem tendsto_cpow_mul_schwartz_atTop (f : SchwartzMap ℝ ℂ) (s : ℂ) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ s * f t) atTop (𝓝 0) := by
  have hpow := ofReal_cpow_isBigO_rpow atTop (eventually_gt_atTop 0) s
  have hf := schwartz_isBigO_atTop_rpow f (-(s.re + 1))
  have h := hpow.mul hf
  have htail : (fun x : ℝ => x ^ s.re * x ^ (-(s.re + 1))) =ᶠ[atTop]
      (fun x : ℝ => x ^ (-(1 : ℝ))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx, show s.re + -(s.re + 1) = -1 by ring]
  exact (h.congr' EventuallyEq.rfl htail).trans_tendsto (tendsto_rpow_neg_atTop zero_lt_one)

private theorem tendsto_cpow_mul_schwartz_zero (f : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun t : ℝ => (t : ℂ) ^ s * f t) (𝓝[>] 0) (𝓝 0) := by
  let l := 𝓝[>] (0 : ℝ)
  have hpow := ofReal_cpow_isBigO_rpow l self_mem_nhdsWithin s
  have h := hpow.mul (schwartz_isBigO_one f l)
  have hp : Tendsto (fun x : ℝ => x ^ s.re) l (𝓝 0) := by
    have hc := Real.continuousAt_rpow_const (0 : ℝ) s.re (Or.inr hs.le)
    rw [ContinuousAt, Real.zero_rpow hs.ne'] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  apply h.trans_tendsto
  simpa only [mul_one] using hp

/-- A derivative of the real radial Schwartz test shifts its Mellin
exponent by one and multiplies the original integral by `-s`. -/
theorem mellin_schwartz_deriv_succ (f : SchwartzMap ℝ ℂ) {s : ℂ} (hs : 0 < s.re) :
    mellin (SchwartzMap.derivCLM ℂ ℂ f) (s + 1) = -s * mellin f s := by
  have hs' : 0 < (s + 1).re := by rw [Complex.add_re, Complex.one_re]; linarith
  have hi := schwartz_mellinConvergent (SchwartzMap.derivCLM ℂ ℂ f) hs'
  have hj := schwartz_mellinConvergent f hs
  have h₁ : IntegrableOn (fun x : ℝ => (x : ℂ) ^ s * deriv f x) (Ioi 0) := by
    simpa only [MellinConvergent, add_sub_cancel_right, smul_eq_mul,
      SchwartzMap.derivCLM_apply] using hi
  have h₂ : IntegrableOn (fun x : ℝ => (s * (x : ℂ) ^ (s - 1)) * f x) (Ioi 0) := by
    have h₀ : IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * f x) (Ioi 0) := hj
    simpa only [IntegrableOn, mul_assoc] using h₀.const_mul s
  have huv := integral_Ioi_mul_deriv_eq_deriv_mul
    (u := fun x : ℝ => (x : ℂ) ^ s) (v := (f : ℝ → ℂ))
    (u' := fun x : ℝ => s * (x : ℂ) ^ (s - 1)) (v' := deriv f)
    (fun x hx => hasDerivAt_ofReal_cpow_const (show x ≠ 0 from (mem_Ioi.1 hx).ne')
      (fun he => by simp [he] at hs))
    (fun x _ => f.differentiableAt.hasDerivAt)
    h₁ h₂ (tendsto_cpow_mul_schwartz_zero f hs) (tendsto_cpow_mul_schwartz_atTop f s)
  simp only [mellin, add_sub_cancel_right, SchwartzMap.derivCLM_apply, smul_eq_mul]
  rw [huv, sub_self, zero_sub]
  simp only [mul_assoc, integral_const_mul, neg_mul]

end Langlands.Analysis
