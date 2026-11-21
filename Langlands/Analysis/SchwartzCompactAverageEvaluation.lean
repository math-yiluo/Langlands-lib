import Langlands.Analysis.SchwartzCompactAverage
import Langlands.Analysis.SchwartzCompactEvaluation

/-! # Evaluating compact averages of uniformly supported Schwartz tests -/

noncomputable section

open MeasureTheory Set
open scoped ContDiff SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis.SchwartzCompactFamilies

open SchwartzCompactAverage

universe u v w

variable {K : Type u} [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
variable {E : Type v} {F : Type w} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A compact average of a family supported on one compact set belongs to the same
supported Schwartz space. -/
def supportedAverage (μ : Measure K) [IsFiniteMeasure μ]
    (w : K → ℂ) (hw : Continuous w) (A : K → E →L[ℝ] F) (hA : Continuous A)
    {B : ℝ} (hB : 0 ≤ B) (hLower : ∀ x k, ‖x‖ ≤ B * ‖A k x‖)
    (Φ : 𝓢(F, ℂ)) (S : Set E) (Q : K → supportedSchwartz S)
    (hQ : ∀ k x, (Q k).val x = Φ (A k x)) : supportedSchwartz S :=
  ⟨average w A Φ μ hw hA hB hLower, fun x hx => by
    rw [average_apply]
    simp only [← hQ, fun k => (Q k).property x hx, mul_zero, integral_zero]⟩

/-- A Schwartz-seminorm-bounded linear functional on the common compact support
commutes with the compact weighted average. Its value on the pullback family is continuous. -/
def SchwartzCompactAverageEvaluationStatement : Prop :=
  ∀ (K : Type u) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [IsFiniteMeasure μ]
    (E : Type v) (F : Type w) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : Set E), IsCompact S → ∀ (L : supportedSchwartz S →ₗ[ℂ] ℂ)
      (q : Seminorm ℝ 𝓢(E, ℂ)), Continuous q → (∀ f, ‖L f‖ ≤ q f.val) →
      ∀ (A : K → E →L[ℝ] F) (hA : Continuous A) (B : ℝ) (hB : 0 ≤ B)
        (hLower : ∀ x k, ‖x‖ ≤ B * ‖A k x‖) (Φ : 𝓢(F, ℂ)) (Q : K → supportedSchwartz S)
        (hQ : ∀ k x, (Q k).val x = Φ (A k x)),
        Continuous (fun k => L (Q k)) ∧
          ∀ (w : K → ℂ) (hw : Continuous w),
            L (supportedAverage μ w hw A hA hB hLower Φ S Q hQ) = ∫ k, w k * L (Q k) ∂μ

theorem schwartzCompactAverageEvaluation : SchwartzCompactAverageEvaluationStatement.{u, v, w} := by
  classical
  intro K _ _ _ _ μ _ E F _ _ _ _ S hS L q hq hBound A hA B hB hLower Φ Q hQ
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨I, T, hT⟩ := exists_compactJet_factor hS L q hq hBound
  let Z := (i : I) → C(S, E [×i.val.2]→L[ℝ] ℂ)
  let : NormedAddCommGroup Z :=
    inferInstanceAs (NormedAddCommGroup ((i : I) → C(S, E [×i.val.2]→L[ℝ] ℂ)))
  let : CompleteSpace Z := inferInstanceAs (CompleteSpace ((i : I) → C(S, E [×i.val.2]→L[ℝ] ℂ)))
  let J (f : supportedSchwartz S) : Z := fun i => derivativeCoordinate S i.val.2 f
  have hEq (k : K) : (⇑(Q k).val : E → ℂ) = Φ ∘ A k := funext (hQ k)
  have hCont : Continuous (fun k => J (Q k)) := by
    apply continuous_pi
    intro i
    apply ContinuousMap.continuous_of_continuous_uncurry
    change Continuous (fun p : K × S => iteratedFDeriv ℝ i.val.2 (⇑(Q p.1).val) p.2.val)
    simp only [hEq]
    exact (continuous_pullbackDerivative A Φ hA i.val.2).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hEval : (fun k => L (Q k)) = T ∘ (fun k => J (Q k)) :=
    funext fun k => (hT (Q k)).symm
  refine ⟨hEval ▸ T.continuous.comp hCont, ?_⟩
  intro weight hw
  let Ψ := supportedAverage μ weight hw A hA hB hLower Φ S Q hQ
  have hWeight : Continuous (fun k : K => weight k • J (Q k)) := hw.smul hCont
  have hI : Integrable (fun k : K => weight k • J (Q k)) μ :=
    hWeight.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hJet : J Ψ = ∫ k, weight k • J (Q k) ∂μ := by
    funext i
    ext1 x
    let proj : Z →L[ℂ] C(S, E [×i.val.2]→L[ℝ] ℂ) := ContinuousLinearMap.proj i
    let ev : Z →L[ℂ] (E [×i.val.2]→L[ℝ] ℂ) := (ContinuousMap.evalCLM ℂ x).comp proj
    change iteratedFDeriv ℝ i.val.2 (⇑Ψ.val) x.val = ev (∫ k, weight k • J (Q k) ∂μ)
    rw [← ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ) (E := Z)
      (Fₗ := E [×i.val.2]→L[ℝ] ℂ) ev hI]
    change iteratedFDeriv ℝ i.val.2 (⇑(average weight A Φ μ hw hA hB hLower)) x.val =
      ∫ k, weight k • iteratedFDeriv ℝ i.val.2 (⇑(Q k).val) x.val ∂μ
    simp only [hEq, iteratedFDeriv_average]
  change L Ψ = _
  rw [← hT Ψ]
  change T (J Ψ) = _
  rw [hJet, ← ContinuousLinearMap.integral_comp_comm (𝕜 := ℂ) (E := Z) T hI]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  change T (weight k • J (Q k)) = weight k * L (Q k)
  rw [map_smul, smul_eq_mul]
  exact congrArg (weight k * ·) (hT (Q k))

end Langlands.Analysis.SchwartzCompactFamilies
