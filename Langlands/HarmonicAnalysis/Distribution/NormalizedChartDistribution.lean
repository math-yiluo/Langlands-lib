import Langlands.HarmonicAnalysis.Distribution.ChartJacobianDensity

/-! # Removing the Jacobian density in local distribution derivatives -/

noncomputable section

open Function Set TopologicalSpace
open scoped ContDiff Distributions

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

section Chart

variable {E X F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {e : OpenPartialHomeomorph E X}
  (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
  (L : E ≃L[ℝ] X)
  {Ω : Opens E} (hΩ : Ω ≤ chartSource e)

include he hei hΩ in
theorem contDiffOn_inv_chartAbsJacobian :
    ContDiffOn ℝ ∞ (fun x => (chartAbsJacobian L e x)⁻¹) Ω :=
  ((contDiffOn_chartAbsJacobian he hei L).mono hΩ).inv fun _ hx =>
    (chartAbsJacobian_pos he hei L (hΩ hx)).ne'

/-- The restriction of a chart distribution after removing the chart
Jacobian density. -/
def jacobianNormalizedChartDistribution (D : 𝓓'((⊤ : Opens X), F)) : 𝓓'(Ω, F) :=
  ((chartFullDistribution e hei D).comp (TestFunction.monoCLM ℝ)).comp
    (localScalarMultiplierCLM (contDiffOn_inv_chartAbsJacobian he hei L hΩ))

/-- Multiplying a test by the chart Jacobian before evaluating the normalized
distribution recovers ordinary chart restriction. -/
theorem jacobianNormalizedChartDistribution_eval_mul_jacobian (D : 𝓓'((⊤ : Opens X), F))
    (f : 𝓓(Ω, ℝ)) :
    jacobianNormalizedChartDistribution he hei L hΩ D
      (localScalarMultiplierCLM ((contDiffOn_chartAbsJacobian he hei L).mono hΩ) f) =
      ((chartFullDistribution e hei D).comp (TestFunction.monoCLM ℝ)) f := by
  let ρ := chartAbsJacobian L e
  let hρ := (contDiffOn_chartAbsJacobian he hei L).mono hΩ
  let hρi := contDiffOn_inv_chartAbsJacobian he hei L hΩ
  have h : localScalarMultiplierCLM hρi (localScalarMultiplierCLM hρ f) = f := by
    ext x
    simp only [localScalarMultiplierCLM_apply]
    by_cases hx : x ∈ Ω
    · rw [mul_assoc, mul_inv_cancel₀ (chartAbsJacobian_pos he hei L (hΩ hx)).ne', mul_one]
    · have hfx : f x = 0 := f.zero_on_compl hx
      simp [hfx]
  unfold jacobianNormalizedChartDistribution
  exact congrArg ((chartFullDistribution e hei D).comp (TestFunction.monoCLM ℝ)) h

/-- If the ambient distribution kills trace-zero linear field derivatives,
its normalized chart distribution kills the constant derivatives generated
by their smooth variable combinations. -/
theorem eval_jacobianNormalizedChartDistribution_constantDerivative_eq_zero
    (D : 𝓓'((⊤ : Opens X), F)) {ι : Type*} [Fintype ι] (A : ι → X →L[ℝ] X)
    (hA : ∀ j, LinearMap.trace ℝ X (A j).toLinearMap = 0)
    (hD : ∀ j (f : 𝓓((⊤ : Opens X), ℝ)),
      D (smoothVectorFieldDerivativeTest (A j).contDiff.contDiffOn f) = 0)
    (u : E) {β : ι → E → ℝ} (hβ : ∀ j, ContDiffOn ℝ ∞ (β j) Ω)
    (hu : ∀ x ∈ Ω, fderiv ℝ e x u = ∑ j, β j x • A j (e x))
    (f : 𝓓(Ω, ℝ)) :
    jacobianNormalizedChartDistribution he hei L hΩ D
      (smoothVectorFieldDerivativeTest (contDiffOn_const (c := u)) f) = 0 := by
  classical
  let V (j : ι) := chartVectorField e (A j)
  have hV (j : ι) : ContDiffOn ℝ ∞ (V j) e.source :=
    contDiffOn_chartVectorField he hei (A j).contDiff.contDiffOn
  let T := (chartFullDistribution e hei D).comp
    (TestFunction.monoCLM ℝ : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(chartSource e, ℝ))
  have hT (j : ι) (g : 𝓓(Ω, ℝ)) :
      T (smoothVectorFieldDerivativeTest ((hV j).mono hΩ) g) = 0 :=
    eval_chartFullDistribution_smoothVectorFieldDerivativeTest_eq_zero e hei D
      (A j).contDiff (hD j) (hV j) hΩ g
  have hsum (x : E) (hx : x ∈ Ω) : u = ∑ j, β j x • V j x := by
    have hc := fderiv_chart_symm_apply_fderiv he hei (hΩ hx) u
    rw [hu x hx, map_sum] at hc
    simpa only [map_smul, V, chartVectorField] using hc.symm
  let b (x : E) := ∑ j, fderiv ℝ (β j) x (V j x)
  have hb : ContDiffOn ℝ ∞ b Ω :=
    ContDiffOn.sum fun j _ =>
      ((hβ j).fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply ((hV j).mono hΩ)
  let ρ := chartAbsJacobian L e
  let hρ := (contDiffOn_chartAbsJacobian he hei L).mono hΩ
  let hρi := contDiffOn_inv_chartAbsJacobian he hei L hΩ
  have hρd (x : E) (hx : x ∈ Ω) : fderiv ℝ ρ x u = ρ x * b x :=
    fderiv_chartAbsJacobian_of_linear_fields he hei L A hA hΩ u hβ hu hx
  let g := localScalarMultiplierCLM hρi f
  have hfg : (f : E → ℝ) = (g : E → ℝ) * ρ := by
    funext x
    change f x = g x * ρ x
    by_cases hx : x ∈ Ω
    · simp only [g, localScalarMultiplierCLM_apply, mul_assoc]
      rw [inv_mul_cancel₀ (chartAbsJacobian_pos he hei L (hΩ hx)).ne', mul_one]
    · have hf : f x = 0 := f.zero_on_compl hx
      have hg : g x = 0 := g.zero_on_compl hx
      rw [hf, hg, zero_mul]
  let hU : ContDiffOn ℝ ∞ (fun _ : E => u) Ω := contDiffOn_const
  have hz := eval_smoothVectorFieldDerivativeTest_add_multiplier_eq_zero T
    (fun j => (hV j).mono hΩ) hβ hT hU hsum hb (fun _ _ => rfl) g
  have heq : localScalarMultiplierCLM hρi (smoothVectorFieldDerivativeTest hU f) =
      smoothVectorFieldDerivativeTest hU g + localScalarMultiplierCLM hb g := by
    ext x
    by_cases hx : x ∈ Ω
    · have hdg := (g.contDiff.differentiable (by simp) x).hasFDerivAt
      have hdρ := ((hρ.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)).hasFDerivAt
      have hn : ρ x ≠ 0 := (chartAbsJacobian_pos he hei L (hΩ hx)).ne'
      change fderiv ℝ f x u * (ρ x)⁻¹ = fderiv ℝ g x u + g x * b x
      rw [hfg, (hdg.mul hdρ).fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul]
      change (g x * fderiv ℝ ρ x u + ρ x * fderiv ℝ g x u) * (ρ x)⁻¹ =
        fderiv ℝ g x u + g x * b x
      rw [hρd x hx]
      field_simp [hn]
      ring
    · exact ((localScalarMultiplierCLM hρi (smoothVectorFieldDerivativeTest hU f)).zero_on_compl hx).trans
        ((smoothVectorFieldDerivativeTest hU g + localScalarMultiplierCLM hb g).zero_on_compl hx).symm
  change T (localScalarMultiplierCLM hρi (smoothVectorFieldDerivativeTest hU f)) = 0
  rw [heq]
  exact hz

end Chart

end Langlands.HarmonicAnalysis
