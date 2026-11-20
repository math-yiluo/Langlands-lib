import Langlands.HarmonicAnalysis.Distribution.FullTestChartTransport
import Langlands.HarmonicAnalysis.Distribution.SmoothVectorFieldTest
import Langlands.HarmonicAnalysis.Distribution.RealMatrixConjugationDerivative

/-! # Transport of distribution derivative identities through a smooth chart -/

noncomputable section

open Filter Set TopologicalSpace
open scoped ContDiff Distributions Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false

namespace Langlands.HarmonicAnalysis

section Chart

variable {E X F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The coordinate vector field obtained by applying the derivative of the
inverse chart to an ambient vector field. -/
def chartVectorField (e : OpenPartialHomeomorph E X) (V : X → X) (x : E) : E :=
  fderiv ℝ e.symm (e x) (V (e x))

theorem contDiffOn_chartVectorField {e : OpenPartialHomeomorph E X}
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {V : X → X} (hV : ContDiffOn ℝ ∞ V e.target) :
    ContDiffOn ℝ ∞ (chartVectorField e V) e.source :=
  (((hei.fderiv_of_isOpen e.open_target (by simp)).clm_apply hV).comp he (fun _ hx => e.map_source hx))

theorem fderiv_chart_symm_apply_fderiv {e : OpenPartialHomeomorph E X}
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    {x : E} (hx : x ∈ e.source) (u : E) :
    fderiv ℝ e.symm (e x) (fderiv ℝ e x u) = u := by
  have hd := (he.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt
    (by simp)
  have hdi := (hei.contDiffAt (e.open_target.mem_nhds (e.map_source hx))).differentiableAt
    (by simp)
  have hleft : (id : E → E) =ᶠ[𝓝 x] e.symm ∘ e := by
    filter_upwards [e.open_source.mem_nhds hx] with z hz
    exact (e.left_inv hz).symm
  have h := ((hdi.hasFDerivAt.comp x hd.hasFDerivAt).congr_of_eventuallyEq hleft).fderiv
  rw [fderiv_id] at h
  exact DFunLike.congr_fun h.symm u

theorem chartTestToFullCLM_smoothVectorFieldDerivativeTest (e : OpenPartialHomeomorph E X)
    (hei : ContDiffOn ℝ ∞ e.symm e.target) {V : X → X} (hV : ContDiff ℝ ∞ V)
    (hVc : ContDiffOn ℝ ∞ (chartVectorField e V) e.source) (f : 𝓓(chartSource e, ℝ)) :
    chartTestToFullCLM e hei (smoothVectorFieldDerivativeTest hVc f) =
      smoothVectorFieldDerivativeTest hV.contDiffOn (chartTestToFullCLM e hei f) := by
  ext y
  rw [smoothVectorFieldDerivativeTest_apply]
  by_cases hy : y ∈ e.target
  · rw [chartTestToFullCLM_apply_of_mem e hei _ hy, smoothVectorFieldDerivativeTest_apply]
    have heq : (chartTestToFullCLM e hei f : X → ℝ) =ᶠ[𝓝 y] (f : E → ℝ) ∘ e.symm := by
      filter_upwards [e.open_target.mem_nhds hy] with z hz
      exact chartTestToFullCLM_apply_of_mem e hei f hz
    have hdi := (hei.contDiffAt (e.open_target.mem_nhds hy)).differentiableAt
      (by simp)
    have hd := (f.contDiff.differentiable (by simp) (e.symm y)).hasFDerivAt
    rw [((hd.comp y hdi.hasFDerivAt).congr_of_eventuallyEq heq).fderiv]
    simp only [ContinuousLinearMap.comp_apply, chartVectorField, e.right_inv hy]
  · rw [chartTestToFullCLM_apply_of_notMem e hei _ hy, fderiv_of_notMem_tsupport ℝ, zero_apply]
    intro hs
    obtain ⟨x, hx, rfl⟩ := tsupport_chartTestToFullCLM_subset e hei f hs
    exact hy (e.map_source (f.tsupport_subset hx))

/-- A derivative annihilated by a full-space distribution remains annihilated
in local coordinates and on every smaller open test domain. -/
theorem eval_chartFullDistribution_smoothVectorFieldDerivativeTest_eq_zero
    (e : OpenPartialHomeomorph E X) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (D : 𝓓'((⊤ : Opens X), F)) {V : X → X} (hV : ContDiff ℝ ∞ V)
    (hD : ∀ f : 𝓓((⊤ : Opens X), ℝ), D (smoothVectorFieldDerivativeTest hV.contDiffOn f) = 0)
    (hVc : ContDiffOn ℝ ∞ (chartVectorField e V) e.source)
    {Ω : Opens E} (hΩ : Ω ≤ chartSource e) (f : 𝓓(Ω, ℝ)) :
    (chartFullDistribution e hei D).comp (TestFunction.monoCLM ℝ)
      (smoothVectorFieldDerivativeTest (hVc.mono hΩ) f) = 0 := by
  let i : 𝓓(Ω, ℝ) →L[ℝ] 𝓓(chartSource e, ℝ) := TestFunction.monoCLM ℝ
  have hcoe (g : 𝓓(Ω, ℝ)) : (i g : E → ℝ) = g := by simp [i, hΩ]
  have hi : i (smoothVectorFieldDerivativeTest (hVc.mono hΩ) f) =
      smoothVectorFieldDerivativeTest hVc (i f) := by
    ext x
    rw [show i (smoothVectorFieldDerivativeTest (hVc.mono hΩ) f) x =
      smoothVectorFieldDerivativeTest (hVc.mono hΩ) f x from congrFun (hcoe _) x]
    simp only [smoothVectorFieldDerivativeTest_apply, hcoe]
  change D (chartTestToFullCLM e hei (i (smoothVectorFieldDerivativeTest (hVc.mono hΩ) f))) = 0
  rw [hi, chartTestToFullCLM_smoothVectorFieldDerivativeTest e hei hV hVc]
  exact hD _

end Chart

namespace RealGeneralLinearDistribution

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/-- Infinitesimal matrix conjugation, expressed in smooth chart coordinates. -/
def chartConjugationVectorField (e : OpenPartialHomeomorph E Mat) (X : Mat) : E → E :=
  chartVectorField e (fun A => X * A - A * X)

private theorem contDiff_commutatorVectorField (X : Mat) :
    ContDiff ℝ ∞ (fun A : Mat => X * A - A * X) := by fun_prop

theorem contDiffOn_chartConjugationVectorField {e : OpenPartialHomeomorph E Mat}
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target) (X : Mat) :
    ContDiffOn ℝ ∞ (chartConjugationVectorField e X) e.source :=
  contDiffOn_chartVectorField he hei (contDiff_commutatorVectorField X).contDiffOn

theorem eval_chartConjugationDerivativeTest_eq_zero {e : OpenPartialHomeomorph E Mat}
    (he : ContDiffOn ℝ ∞ e e.source) (hei : ContDiffOn ℝ ∞ e.symm e.target)
    (D : FullDistribution n) (hD : IsFullConjugationInvariant D)
    {Ω : Opens E} (hΩ : Ω ≤ chartSource e) (X : Mat) (f : 𝓓(Ω, ℝ)) :
    (chartFullDistribution e hei D).comp (TestFunction.monoCLM ℝ)
      (smoothVectorFieldDerivativeTest
        ((contDiffOn_chartConjugationVectorField he hei X).mono hΩ) f) = 0 := by
  apply eval_chartFullDistribution_smoothVectorFieldDerivativeTest_eq_zero
    e hei D (contDiff_commutatorVectorField X) _ (contDiffOn_chartConjugationVectorField he hei X) hΩ
  intro g
  have hg : smoothVectorFieldDerivativeTest (contDiff_commutatorVectorField X).contDiffOn g =
      fullConjugationDerivativeTest X g := by
    ext x
    exact (fullConjugationDerivativeTest_apply X (g : FullTest n) x).symm
  rw [hg]
  exact eval_fullConjugationDerivativeTest_eq_zero D hD X g

end RealGeneralLinearDistribution

end Langlands.HarmonicAnalysis
