import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Joint continuity across a removable point by the Cauchy integral formula

Let `f(s, x)` be holomorphic in `s` on an open set `W ⊆ ℂ` for every `x` of a topological
space `X`, and jointly continuous on `(W \ {s₀}) × X`. Then `f` is jointly continuous on
`B × X` for a disc `B` around `s₀`: the Cauchy integral formula on a circle around `s₀`
writes `f(s, x)` as an integral over the circle of a function jointly continuous in
`(s, x)` and the point of the circle. -/

noncomputable section

set_option autoImplicit false

open Set Metric Filter Topology Complex
open scoped Real

namespace Langlands.Analysis

variable {X : Type*} [TopologicalSpace X]

/-- **Joint continuity across a removable point.** If `s ↦ f s x` is complex differentiable on
the open set `W ∋ s₀` for every `x` and `(s, x) ↦ f s x` is continuous on `(W \ {s₀}) × X`,
then `(s, x) ↦ f s x` is continuous on `ball s₀ ρ × X` for some `ρ > 0` with
`ball s₀ ρ ⊆ W`. -/
theorem exists_ball_continuousOn_of_punctured {f : ℂ → X → ℂ} {W : Set ℂ} (hW : IsOpen W)
    {s₀ : ℂ} (hs₀ : s₀ ∈ W) (hd : ∀ x, DifferentiableOn ℂ (fun s => f s x) W)
    (hc : ContinuousOn (fun q : ℂ × X => f q.1 q.2) ((W \ {s₀}) ×ˢ univ)) :
    ∃ ρ > 0, ball s₀ ρ ⊆ W ∧ ContinuousOn (fun q : ℂ × X => f q.1 q.2) (ball s₀ ρ ×ˢ univ) := by
  obtain ⟨ε, hε, hεW⟩ := Metric.isOpen_iff.mp hW s₀ hs₀
  set R : ℝ := ε / 2 with hRdef
  have hR : 0 < R := half_pos hε
  have hRε : R < ε := half_lt_self hε
  have hcl : closedBall s₀ R ⊆ W := (closedBall_subset_ball hRε).trans hεW
  set ρ : ℝ := R / 2 with hρdef
  have hρ : 0 < ρ := half_pos hR
  have hρR : ρ < R := half_lt_self hR
  refine ⟨ρ, hρ, (ball_subset_ball hρR.le).trans (ball_subset_closedBall.trans hcl), ?_⟩
  -- the integrand of the Cauchy formula, as a function of `((s, x), θ)`
  let S : Set (ℂ × X) := ball s₀ ρ ×ˢ univ
  let k : S → ℝ → ℂ := fun q θ =>
    deriv (circleMap s₀ R) θ • ((circleMap s₀ R θ - (q : ℂ × X).1)⁻¹ •
      f (circleMap s₀ R θ) (q : ℂ × X).2)
  have hmemW : ∀ θ : ℝ, circleMap s₀ R θ ∈ W \ {s₀} := fun θ =>
    ⟨hcl (sphere_subset_closedBall (circleMap_mem_sphere s₀ hR.le θ)),
      circleMap_ne_center hR.ne'⟩
  have hne : ∀ (q : S) (θ : ℝ), circleMap s₀ R θ - (q : ℂ × X).1 ≠ 0 := by
    intro q θ
    rw [sub_ne_zero]
    intro h
    have hq : (q : ℂ × X).1 ∈ ball s₀ ρ := q.2.1
    have h1 : dist (circleMap s₀ R θ) s₀ = R :=
      mem_sphere.mp (circleMap_mem_sphere s₀ hR.le θ)
    rw [h] at h1
    exact absurd (mem_ball.mp hq) (by rw [h1]; exact not_lt.mpr hρR.le)
  have hk : Continuous (Function.uncurry k) := by
    have hcm : Continuous fun p : S × ℝ => circleMap s₀ R p.2 :=
      (continuous_circleMap s₀ R).comp continuous_snd
    have hderiv : Continuous fun p : S × ℝ => deriv (circleMap s₀ R) p.2 := by
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 R).comp continuous_snd).mul continuous_const
    have hfst : Continuous fun p : S × ℝ => ((p.1 : ℂ × X)).1 :=
      continuous_fst.comp (continuous_subtype_val.comp continuous_fst)
    have hsnd : Continuous fun p : S × ℝ => ((p.1 : ℂ × X)).2 :=
      continuous_snd.comp (continuous_subtype_val.comp continuous_fst)
    have hinv : Continuous fun p : S × ℝ => (circleMap s₀ R p.2 - ((p.1 : ℂ × X)).1)⁻¹ :=
      (hcm.sub hfst).inv₀ fun p => hne p.1 p.2
    have hf : Continuous fun p : S × ℝ => f (circleMap s₀ R p.2) ((p.1 : ℂ × X)).2 := by
      refine hc.comp_continuous (hcm.prodMk hsnd) fun p => ⟨hmemW p.2, mem_univ _⟩
    exact hderiv.smul (hinv.smul hf)
  have hint : Continuous fun q : S => ∫ θ in (0 : ℝ)..2 * π, k q θ :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hk 0 (2 * π)
  -- the Cauchy formula on the circle of radius `R`
  have hcauchy : ∀ q : S, f (q : ℂ × X).1 (q : ℂ × X).2 =
      (2 * π * I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, k q θ := by
    intro q
    have hw : (q : ℂ × X).1 ∈ ball s₀ R := ball_subset_ball hρR.le q.2.1
    have := ((hd (q : ℂ × X).2).mono hcl).circleIntegral_sub_inv_smul hw
    rw [circleIntegral] at this
    change ∫ θ in (0 : ℝ)..2 * π, k q θ = _ at this
    rw [this, smul_smul, inv_mul_cancel₀ (by simp [Real.pi_ne_zero]), one_smul]
  rw [continuousOn_iff_continuous_domRestrict]
  have heq : S.domRestrict (fun q : ℂ × X => f q.1 q.2) =
      fun q : S => (2 * π * I : ℂ)⁻¹ • ∫ θ in (0 : ℝ)..2 * π, k q θ := by
    funext q
    exact hcauchy q
  rw [heq]
  exact hint.const_smul ((2 * π * I : ℂ)⁻¹)

end Langlands.Analysis
