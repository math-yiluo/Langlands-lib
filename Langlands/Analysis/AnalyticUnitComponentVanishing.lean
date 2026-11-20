import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Normed.Ring.Units

/-! # Analytic componentwise vanishing for differential-stable families -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option Elab.async false

open Filter Set NormedSpace
open scoped Topology

namespace Langlands.Analysis

universe uA uV

/-- A real analytic family on the unit group, closed under the directional
derivatives in directions `g * X`, vanishes on a whole component when every
member vanishes at one point in that component. -/
def AnalyticUnitComponentVanishingStatement : Prop :=
  ∀ {A : Type uA} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    {V : Type uV} (f : V → A → ℂ) (D : A → V → V),
    (∀ v (g : Aˣ), AnalyticAt ℝ (f v) (g : A)) →
    (∀ X v (g : Aˣ), fderiv ℝ (f v) (g : A) ((g : A) * X) = f (D X v) (g : A)) →
    ∀ p : Aˣ, (∀ v, f v (p : A) = 0) →
      ∀ g ∈ connectedComponent p, ∀ v, f v (g : A) = 0

theorem analyticUnitComponentVanishing : AnalyticUnitComponentVanishingStatement.{uA, uV} := by
  intro A _ _ _ V f D han hD p hzero
  have hExp (X : A) :
      ∀ (v : V) (t : ℝ), f v ((p : A) * exp (t • X)) = 0 := by
    let a (t : ℝ) := (p : A) * exp (t • X)
    have hu (t : ℝ) : IsUnit (exp (t • X)) :=
      isUnit_exp_of_mem_ball (𝕂 := ℝ) (by rw [expSeries_radius_eq_top]; exact edist_lt_top _ _)
    let q (t : ℝ) : Aˣ := p * (hu t).unit
    let c (v : V) (t : ℝ) := f v (a t)
    have hq (t : ℝ) : (q t : A) = a t := by simp only [q, a, Units.val_mul, IsUnit.unit_spec]
    have ha (t : ℝ) : AnalyticAt ℝ a t := by
      have hsmul : AnalyticAt ℝ (fun s : ℝ => s • X) t :=
        analyticAt_id.smul analyticAt_const
      have he : AnalyticAt ℝ (exp : A → A) (t • X) := exp_analytic _
      exact analyticAt_const.mul (he.comp_of_eq hsmul rfl)
    have hc (v : V) (t : ℝ) : AnalyticAt ℝ (c v) t := by
      simpa only [c, Function.comp_def] using ((hq t ▸ han v (q t))).comp (ha t)
    have hderiv (v : V) : deriv (c v) = c (D X v) := by
      funext t
      have hcurve : HasDerivAt a (a t * X) t := by
        simpa only [a, mul_assoc] using (hasDerivAt_exp_smul_const X t).const_mul (p : A)
      have hf : DifferentiableAt ℝ (f v) (a t) := hq t ▸ (han v (q t)).differentiableAt
      have h := (hf.hasFDerivAt.comp_hasDerivAt t hcurve).deriv
      exact h.trans (hq t ▸ hD X v (q t))
    have hjet (m : ℕ) (v : V) : iteratedDeriv m (c v) 0 = 0 := by
      induction m generalizing v with
      | zero => simpa only [iteratedDeriv_zero, c, a, zero_smul, exp_zero, mul_one] using hzero v
      | succ m ih => rw [iteratedDeriv_succ', hderiv]; exact ih (D X v)
    intro v t
    have htop : analyticOrderAt (c v) 0 = ⊤ := by
      apply eq_top_iff.mpr
      rw [← ENat.iSup_natCast]
      exact iSup_le fun m =>
        (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hc v 0)).mpr
          (fun j _ => hjet j v)
    exact congrFun ((AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero 0 (hc v)).mp htop) t
  have hexpNhds : map (exp : A → A) (𝓝 (0 : A)) = 𝓝 (1 : A) := by
    have h : HasStrictFDerivAt (exp : A → A) (1 : A →L[ℝ] A) 0 := hasStrictFDerivAt_exp_zero
    simpa only [exp_zero] using
      h.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr fun x => ⟨x, rfl⟩)
  have hlocal (v : V) : f v =ᶠ[𝓝 (p : A)] 0 := by
    let L := (ContinuousAddEquiv.mulLeft p).toHomeomorph
    have hLp : L (1 : A) = (p : A) := mul_one _
    have hL : map L (𝓝 (1 : A)) = 𝓝 (p : A) := by
      rw [← hLp]
      exact L.map_nhds_eq (1 : A)
    change ∀ᶠ x in 𝓝 (p : A), f v x = 0
    rw [← hL, ← hexpNhds, Filter.map_map]
    apply Filter.eventually_map.mpr
    exact Eventually.of_forall fun X => by
      change f v ((p : A) * exp X) = 0
      simpa only [one_smul] using hExp X v (1 : ℝ)
  let S := (Units.val : Aˣ → A) '' connectedComponent p
  have hS : IsPreconnected S :=
    isPreconnected_connectedComponent.image _ Units.continuous_val.continuousOn
  intro g hg v
  have hAn : AnalyticOnNhd ℝ (f v) S := by
    rintro _ ⟨x, _, rfl⟩
    exact han v x
  have hp : (p : A) ∈ S := mem_image_of_mem _ mem_connectedComponent
  exact hAn.eqOn_zero_of_preconnected_of_eventuallyEq_zero hS hp (hlocal v)
    (mem_image_of_mem _ hg)

end Langlands.Analysis
