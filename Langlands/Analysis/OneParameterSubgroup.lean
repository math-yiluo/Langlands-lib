import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Continuous one-parameter subgroups of a Banach algebra

`exists_exp_smul_of_continuous_oneParameter`: a continuous `m : ℝ → A` into a complete normed
`ℝ`-algebra with `m 0 = 1` and `m (s + t) = m s * m t` is `t ↦ exp (t • X)` for some `X ∈ A`.

Proof: for small `ε > 0` the integral `B = ∫₀^ε m` is invertible (it is close to `ε`), and
`m t = (∫₀^{t+ε} m - ∫₀^t m) B⁻¹` is differentiable with `m' = m X`, `X = (m ε - 1) B⁻¹`; then
`m t · exp (-t X)` has derivative `0` and is constant.
-/

open MeasureTheory

namespace Langlands

/-- A continuous one-parameter subgroup of a Banach algebra is `t ↦ exp (t • X)`. -/
theorem exists_exp_smul_of_continuous_oneParameter {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] (m : ℝ → A) (hc : Continuous m)
    (h0 : m 0 = 1) (hm : ∀ s t, m (s + t) = m s * m t) : ∃ X : A, ∀ t, m t = NormedSpace.exp (t • X) := by
  have hI : ∀ t, HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, m s) (m t) t := fun t =>
    intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _) (hc.stronglyMeasurableAtFilter _ _)
      hc.continuousAt
  obtain ⟨ε, hε, hu⟩ : ∃ ε : ℝ, 0 < ε ∧ IsUnit (∫ s in (0 : ℝ)..ε, m s) := by
    have h1 := (hasDerivAt_iff_tendsto_slope_zero.1 (hI 0))
    simp only [zero_add, intervalIntegral.integral_same, sub_zero, h0] at h1
    have h2 : ∀ᶠ t in nhdsWithin (0 : ℝ) {0}ᶜ, IsUnit (t⁻¹ • ∫ s in (0 : ℝ)..t, m s) :=
      h1.eventually (Units.isOpen.mem_nhds isUnit_one)
    have h3 : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), IsUnit (t⁻¹ • ∫ s in (0 : ℝ)..t, m s) :=
      h2.filter_mono (nhdsWithin_mono _ fun x hx => ne_of_gt hx)
    obtain ⟨t, ht, ht0⟩ := (h3.and self_mem_nhdsWithin).exists
    refine ⟨t, ht0, ?_⟩
    have : (∫ s in (0 : ℝ)..t, m s) = algebraMap ℝ A t * (t⁻¹ • ∫ s in (0 : ℝ)..t, m s) := by
      rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ (ne_of_gt ht0), one_smul]
    rw [this]
    exact ((IsUnit.mk0 t (ne_of_gt ht0)).map (algebraMap ℝ A)).mul ht
  obtain ⟨B, hB⟩ := hu
  have key : ∀ t, m t = ((∫ s in (0 : ℝ)..(t + ε), m s) - ∫ s in (0 : ℝ)..t, m s) * (B⁻¹ : Aˣ) := fun t => by
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _)]
    have e : (∫ s in t..(t + ε), m s) = m t * B := by
      have e0 := (ContinuousLinearMap.mul ℝ A (m t)).intervalIntegral_comp_comm (hc.intervalIntegrable (μ := volume) 0 ε)
      rw [hB, ← ContinuousLinearMap.mul_apply' ℝ A, ← e0]
      have := intervalIntegral.integral_comp_add_left m (a := 0) (b := ε) t
      rw [add_zero] at this
      rw [← this]
      simp [hm]
    rw [e, mul_assoc, Units.mul_inv, mul_one]
  set X : A := (m ε - 1) * (B⁻¹ : Aˣ) with hX
  have hd : ∀ t, HasDerivAt m (m t * X) t := fun t => by
    have h1 := (((hI (t + ε)).comp_add_const t ε).sub (hI t)).mul_const ((B⁻¹ : Aˣ) : A)
    have h2 : (m (t + ε) - m t) * ((B⁻¹ : Aˣ) : A) = m t * X := by rw [hX, hm, ← mul_assoc, mul_sub, mul_one]
    rw [h2] at h1
    exact h1.congr_of_eventuallyEq (.of_forall key)
  refine ⟨X, fun t => ?_⟩
  let : NormedAlgebra ℚ A := NormedAlgebra.restrictScalars ℚ ℝ A
  have hg : ∀ s, HasDerivAt (fun s => m s * NormedSpace.exp (s • (-X))) 0 s := fun s => by
    have := (hd s).mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-X) s)
    exact this.congr_deriv (by simp [mul_assoc])
  have hk : m t * NormedSpace.exp (t • (-X)) = 1 := by
    have := is_const_of_deriv_eq_zero (fun s => (hg s).differentiableAt) (fun s => (hg s).deriv) t 0
    simpa [h0] using this
  have h2 : NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X) = 1 := by
    rw [← NormedSpace.exp_add_of_commute (((Commute.refl X).neg_left.smul_left t).smul_right t)]
    simp
  calc m t = m t * (NormedSpace.exp (t • (-X)) * NormedSpace.exp (t • X)) := by rw [h2, mul_one]
    _ = _ := by rw [← mul_assoc, hk, one_mul]

end Langlands
