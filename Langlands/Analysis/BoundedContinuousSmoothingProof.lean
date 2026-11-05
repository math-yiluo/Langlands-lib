import Langlands.Analysis.BoundedContinuousSmoothingStatement
import Langlands.Analysis.HilbertSchmidtEvaluationProof
import Langlands.Analysis.TraceClassIdealProof

noncomputable section

open MeasureTheory Filter
open scoped MeasureTheory BoundedContinuousFunction

namespace Langlands.Analysis.OperatorIdeals

universe u v w

theorem hilbertSchmidtBoundedContinuousLift :
    HilbertSchmidtBoundedContinuousLiftStatement.{u, v} := by
  intro E _ _ _ X _ _ _ μ _ j A S hS
  let B : E →L[ℂ] Lp ℂ 2 μ := j.toContinuousLinearMap.comp A
  let k : X → E →L[ℂ] ℂ := fun x =>
    (BoundedContinuousFunction.evalCLM ℂ x).comp S
  have hrep : ∀ z : E, (B z : X → ℂ) =ᵐ[μ] fun x => k x z := by
    intro z
    change (j (A z) : X → ℂ) =ᵐ[μ] fun x => S z x
    rw [hS z]
    exact BoundedContinuousFunction.coeFn_toLp 2 μ ℂ (S z)
  have hbound : ∀ᵐ x ∂μ, ‖k x‖ ≤ ‖S‖ := by
    apply Eventually.of_forall
    intro x
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg S)
    intro z
    exact (S z).norm_coe_le_norm x |>.trans (S.le_opNorm z)
  have hB := (hilbertSchmidtUniformEvaluation.{u, v, u} E X μ B k ‖S‖
    (norm_nonneg _) hrep hbound).1
  obtain ⟨s, b, hb⟩ := hB
  refine ⟨s, b, ?_⟩
  simpa only [B, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    j.norm_map] using hb

theorem traceClassFiniteFactorizationSmoothing :
    TraceClassFiniteFactorizationSmoothingStatement.{u, v, w} := by
  intro E _ _ _ X _ _ _ μ _ T _ _ _ _ j R hS hfactor
  have hHS : ∀ f : T, IsHilbertSchmidt (R f) := by
    intro f
    obtain ⟨S, hS⟩ := hS f
    exact hilbertSchmidtBoundedContinuousLift E X μ j (R f) S hS
  intro f
  obtain ⟨n, a, b, hf⟩ := hfactor f
  have hprod (i : Fin n) : IsTraceClass (R (a i * b i)) := by
    rw [map_mul, ContinuousLinearMap.mul_def]
    exact hilbertSchmidtProductTraceClass E E (R (b i)) (R (a i))
      (hHS (b i)) (hHS (a i))
  have hsum (s : Finset (Fin n)) : IsTraceClass (∑ i ∈ s, R (a i * b i)) := by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using (isTraceClass_zero (E := E))
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact isTraceClass_add _ _ (hprod i) ih
  rw [hf, map_sum]
  exact hsum Finset.univ

theorem boundedContinuousSmoothingCriteria :
    BoundedContinuousSmoothingCriteriaStatement.{u, v, w} := by
  exact ⟨hilbertSchmidtBoundedContinuousLift, traceClassFiniteFactorizationSmoothing⟩

end Langlands.Analysis.OperatorIdeals
