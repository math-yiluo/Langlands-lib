import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric

/-! # Holomorphy of integrals with exponential moments

For a measure `μ`, a complex function `A` and a real function `L` such that
`‖A‖ exp (σ L)` is integrable for every real `σ`, the integral
`s ↦ ∫ A exp (s L) dμ` converges absolutely for every complex `s`, is differentiable on `ℂ`,
and is bounded on every closed vertical strip. -/

noncomputable section
set_option autoImplicit false

open MeasureTheory Metric

namespace Langlands.Global.RankinSelbergGlobal.UnequalAnalytic

/-! ### Real exponential inequalities -/

/-- On `[a, b]`, `exp (σ L)` is at most `exp (a L) + exp (b L)`. -/
theorem exp_mul_le_add {a b σ : ℝ} (L : ℝ) (ha : a ≤ σ) (hb : σ ≤ b) :
    Real.exp (σ * L) ≤ Real.exp (a * L) + Real.exp (b * L) := by
  rcases le_total 0 L with hL | hL
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hb hL)).trans
      (le_add_of_nonneg_left (Real.exp_pos _).le)
  · exact (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right ha hL)).trans
      (le_add_of_nonneg_right (Real.exp_pos _).le)

/-- `|L| ≤ exp L + exp (-L)`. -/
theorem abs_le_exp_add_exp_neg (L : ℝ) : |L| ≤ Real.exp L + Real.exp (-L) := by
  have h1 := Real.add_one_le_exp L
  have h2 := Real.add_one_le_exp (-L)
  rcases le_total 0 L with hL | hL
  · rw [abs_of_nonneg hL]; linarith [Real.exp_pos (-L)]
  · rw [abs_of_nonpos hL]; linarith [Real.exp_pos L]

/-- Near `a`, `|L| exp (σ L)` is bounded by four exponentials independent of `σ`. -/
theorem abs_mul_exp_le {a σ : ℝ} (L : ℝ) (h : |σ - a| ≤ 1) :
    |L| * Real.exp (σ * L) ≤
      Real.exp ((a + 2) * L) + 2 * Real.exp (a * L) + Real.exp ((a - 2) * L) := by
  have h' := abs_le.mp h
  have he := exp_mul_le_add (a := a - 1) (b := a + 1) (σ := σ) L (by linarith) (by linarith)
  have hl := abs_le_exp_add_exp_neg L
  calc |L| * Real.exp (σ * L)
      ≤ (Real.exp L + Real.exp (-L)) * (Real.exp ((a - 1) * L) + Real.exp ((a + 1) * L)) :=
        mul_le_mul hl he (Real.exp_pos _).le (by positivity)
    _ = Real.exp ((a + 2) * L) + 2 * Real.exp (a * L) + Real.exp ((a - 2) * L) := by
        simp only [add_mul, mul_add, ← Real.exp_add]
        ring_nf

/-! ### Integrals with exponential moments -/

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {A : X → ℂ} {L : X → ℝ}

/-- The norm of `A exp (s L)`. -/
theorem norm_mul_cexp (A : ℂ) (s : ℂ) (L : ℝ) :
    ‖A * Complex.exp (s * L)‖ = ‖A‖ * Real.exp (s.re * L) := by
  rw [norm_mul, Complex.norm_exp]
  congr 2
  simp

theorem aestronglyMeasurable_mul_cexp (hA : AEStronglyMeasurable A μ)
    (hL : AEStronglyMeasurable L μ) (s : ℂ) :
    AEStronglyMeasurable (fun x => A x * Complex.exp (s * L x)) μ :=
  hA.mul (Complex.continuous_exp.comp_aestronglyMeasurable
    ((Complex.continuous_ofReal.comp_aestronglyMeasurable hL).const_mul s))

/-- Absolute convergence for every complex parameter. -/
theorem integrable_mul_cexp (hA : AEStronglyMeasurable A μ) (hL : AEStronglyMeasurable L μ)
    (hint : ∀ σ : ℝ, Integrable (fun x => ‖A x‖ * Real.exp (σ * L x)) μ) (s : ℂ) :
    Integrable (fun x => A x * Complex.exp (s * L x)) μ := by
  refine (hint s.re).mono' (aestronglyMeasurable_mul_cexp hA hL s) ?_
  exact Filter.Eventually.of_forall fun x => (norm_mul_cexp _ _ _).le

/-- **Holomorphy.** The integral is complex differentiable everywhere. -/
theorem differentiable_integral_mul_cexp (hA : AEStronglyMeasurable A μ)
    (hL : AEStronglyMeasurable L μ)
    (hint : ∀ σ : ℝ, Integrable (fun x => ‖A x‖ * Real.exp (σ * L x)) μ) :
    Differentiable ℂ (fun s : ℂ => ∫ x, A x * Complex.exp (s * L x) ∂μ) := by
  intro s₀
  let F' : ℂ → X → ℂ := fun s x => A x * (Complex.exp (s * L x) * L x)
  let bound : X → ℝ := fun x => ‖A x‖ * (Real.exp ((s₀.re + 2) * L x) +
    2 * Real.exp (s₀.re * L x) + Real.exp ((s₀.re - 2) * L x))
  have hF'meas : AEStronglyMeasurable (F' s₀) μ := by
    refine hA.mul ?_
    exact (Complex.continuous_exp.comp_aestronglyMeasurable
      ((Complex.continuous_ofReal.comp_aestronglyMeasurable hL).const_mul s₀)).mul
      (Complex.continuous_ofReal.comp_aestronglyMeasurable hL)
  have hbound : Integrable bound μ := by
    have h := ((hint (s₀.re + 2)).add ((hint s₀.re).const_mul 2)).add (hint (s₀.re - 2))
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply, bound]
    ring
  have hle : ∀ x, ∀ s ∈ ball s₀ 1, ‖F' s x‖ ≤ bound x := by
    intro x s hs
    have hre : |s.re - s₀.re| ≤ 1 := by
      have h1 : |(s - s₀).re| ≤ ‖s - s₀‖ := Complex.abs_re_le_norm _
      rw [Complex.sub_re] at h1
      exact (h1.trans (mem_ball_iff_norm.mp hs).le)
    simp only [F', bound, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    rw [show (s * (L x : ℂ)).re = s.re * L x by simp]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    rw [mul_comm]
    exact abs_mul_exp_le (L x) hre
  have hderiv : ∀ x, ∀ s ∈ ball s₀ 1,
      HasDerivAt (fun s : ℂ => A x * Complex.exp (s * L x)) (F' s x) s := by
    intro x s _
    have h := HasDerivAt.const_mul (A x)
      (HasDerivAt.cexp (HasDerivAt.mul_const (hasDerivAt_id s) (L x : ℂ)))
    simpa only [id, one_mul, F'] using h
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le (ball_mem_nhds s₀ one_pos)
    (Filter.Eventually.of_forall fun s => aestronglyMeasurable_mul_cexp hA hL s)
    (integrable_mul_cexp hA hL hint s₀) hF'meas
    (Filter.Eventually.of_forall hle) hbound
    (Filter.Eventually.of_forall hderiv)).2.differentiableAt

/-- **Boundedness in vertical strips.** On `a ≤ re s ≤ b` the integral is bounded. -/
theorem exists_norm_integral_mul_cexp_le
    (hint : ∀ σ : ℝ, Integrable (fun x => ‖A x‖ * Real.exp (σ * L x)) μ) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, a ≤ s.re → s.re ≤ b →
      ‖∫ x, A x * Complex.exp (s * L x) ∂μ‖ ≤ C := by
  refine ⟨∫ x, (‖A x‖ * Real.exp (a * L x) + ‖A x‖ * Real.exp (b * L x)) ∂μ,
    integral_nonneg fun x => by positivity, fun s ha hb => ?_⟩
  refine norm_integral_le_of_norm_le ((hint a).add (hint b))
    (Filter.Eventually.of_forall fun x => ?_)
  rw [norm_mul_cexp, ← mul_add]
  exact mul_le_mul_of_nonneg_left (exp_mul_le_add (L x) ha hb) (norm_nonneg _)

end Langlands.Global.RankinSelbergGlobal.UnequalAnalytic
