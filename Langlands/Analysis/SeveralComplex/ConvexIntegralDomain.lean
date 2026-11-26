import Langlands.Analysis.SeveralComplex.ParametricIntegral
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # Holomorphy on the interior of an integral's domain of absolute convergence -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.SeveralComplex

open MeasureTheory Set Filter Metric Topology

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {n : ℕ}
  {f : (Fin n → ℂ) → X → ℂ}

/-- The norm of a constant times the exponential of a complex linear form is real convex. -/
theorem convexOn_norm_mul_cexp_linear (a : ℂ) (L : (Fin n → ℂ) →ₗ[ℂ] ℂ) :
    ConvexOn ℝ univ (fun s => ‖a * Complex.exp (L s)‖) := by
  simp only [norm_mul, Complex.norm_exp]
  change ConvexOn ℝ univ (fun s => ‖a‖ • Real.exp (Complex.reLm (L s)))
  simpa only [Function.comp_apply, Set.preimage_univ, LinearMap.comp_apply,
    LinearMap.restrictScalars_apply] using
    (convexOn_exp.comp_linearMap (Complex.reLm.comp (L.restrictScalars ℝ))).smul (norm_nonneg a)

/-- Pointwise convexity of the norm implies convexity of the domain of absolute convergence. -/
theorem convex_setOf_integrable
    (hmeas : ∀ s, AEStronglyMeasurable (f s) μ)
    (hconv : ∀ x, ConvexOn ℝ univ (fun s => ‖f s x‖)) :
    Convex ℝ {s | Integrable (f s) μ} := by
  intro s hs t ht a b ha hb hab
  have hbound := (hs.norm.const_mul a).add (ht.norm.const_mul b)
  exact hbound.mono' (hmeas _) (Eventually.of_forall fun x =>
    (hconv x).2 (mem_univ s) (mem_univ t) ha hb hab)

/-- The integral of an entire family with pointwise convex norms is holomorphic on the
interior of its domain of absolute convergence. Nearby points lie in the convex hull of
finitely many integrable parameters, and the sum of their norms is a local majorant. -/
theorem differentiableOn_integral_interior_of_convex_norm
    (hdiff : ∀ x, Differentiable ℂ (fun s => f s x))
    (hmeas : ∀ s, AEStronglyMeasurable (f s) μ)
    (hconv : ∀ x, ConvexOn ℝ univ (fun s => ‖f s x‖)) :
    DifferentiableOn ℂ (fun s => ∫ x, f s x ∂μ) (interior {s | Integrable (f s) μ}) := by
  intro s₀ hs₀
  obtain ⟨p, hp, hpint⟩ := exists_mem_interior_convexHull_affineBasis (mem_interior_iff_mem_nhds.mp hs₀)
  obtain ⟨ε, hε, hball⟩ := isOpen_iff.1 isOpen_interior s₀ hp
  let r := ε / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have htwo : closedBall s₀ (2 * r) ⊆ convexHull ℝ (range p) :=
    (closedBall_subset_ball (by dsimp [r]; linarith)).trans (hball.trans interior_subset)
  let b : X → ℝ := fun x => ∑ i, ‖f (p i) x‖
  have hb : Integrable b μ :=
    integrable_finsetSum _ fun i _ => (hpint (subset_convexHull ℝ _ (mem_range_self i))).norm
  have hbd (x : X) (s) (hs : s ∈ convexHull ℝ (range p)) : ‖f s x‖ ≤ b x := by
    have hc : Convex ℝ {z | ‖f z x‖ ≤ b x} := by simpa using (hconv x).convex_le (b x)
    refine convexHull_min (fun y hy => ?_) hc hs
    obtain ⟨i, rfl⟩ := hy
    exact Finset.single_le_sum (fun j _ => norm_nonneg (f (p j) x)) (Finset.mem_univ i)
  have hderiv (x : X) (s) (hs : s ∈ ball s₀ r) :
      ‖fderiv ℂ (fun t => f t x) s‖ ≤ b x / r := by
    refine norm_fderiv_le isOpen_univ (hdiff x).differentiableOn hr (subset_univ _) ?_
    intro t ht
    apply hbd x t
    apply htwo
    rw [mem_ball] at hs
    rw [mem_closedBall] at ht ⊢
    exact (dist_triangle t s s₀).trans (by linarith)
  refine (hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F' := fun s x => fderiv ℂ (fun t => f t x) s) (bound := fun x => b x / r)
    (ball_mem_nhds s₀ hr) (Eventually.of_forall hmeas) (hpint (interior_subset hp)) ?_
    (Eventually.of_forall hderiv) (hb.div_const r)
    (Eventually.of_forall fun x s _ => (hdiff x s).hasFDerivAt)
    ).differentiableAt.differentiableWithinAt
  exact aestronglyMeasurable_fderiv f hr (fun s _ => hmeas s) (fun x => hdiff x s₀)

end Langlands.Analysis.SeveralComplex
