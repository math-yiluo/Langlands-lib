import Langlands.Analysis.OperatorIdeals
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace Langlands.Analysis.OperatorIdeals

universe u v w

/-- An integrable bound for the squared norms of pointwise evaluation functionals
bounds every Hilbert–Schmidt basis sum of the represented operator. -/
def HilbertSchmidtDominatedEvaluationStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X : Type v) [MeasurableSpace X] (μ : Measure X)
    (A : E →L[ℂ] Lp ℂ 2 μ) (k : X → E →L[ℂ] ℂ) (g : X → ℝ),
    Integrable g μ →
    (∀ z : E, (A z : X → ℂ) =ᵐ[μ] fun x => k x z) →
    (∀ᵐ x ∂μ, ‖k x‖ ^ 2 ≤ g x) →
    IsHilbertSchmidt A ∧
      ∀ (ι : Type w) (b : HilbertBasis ι ℂ E),
        Summable (fun i => ‖A (b i)‖ ^ 2) ∧
          (∑' i, ‖A (b i)‖ ^ 2) ≤ ∫ x, g x ∂μ

/-- On a finite measure space, a uniform evaluation bound gives a quantitative
Hilbert–Schmidt criterion. -/
def HilbertSchmidtUniformEvaluationStatement : Prop :=
  ∀ (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (X : Type v) [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (A : E →L[ℂ] Lp ℂ 2 μ) (k : X → E →L[ℂ] ℂ) (C : ℝ),
    0 ≤ C →
    (∀ z : E, (A z : X → ℂ) =ᵐ[μ] fun x => k x z) →
    (∀ᵐ x ∂μ, ‖k x‖ ≤ C) →
    IsHilbertSchmidt A ∧
      ∀ (ι : Type w) (b : HilbertBasis ι ℂ E),
        Summable (fun i => ‖A (b i)‖ ^ 2) ∧
          (∑' i, ‖A (b i)‖ ^ 2) ≤ C ^ 2 * (μ Set.univ).toReal

/-- The dominated and finite-measure uniform evaluation criteria. -/
def HilbertSchmidtEvaluationCriteriaStatement : Prop :=
  HilbertSchmidtDominatedEvaluationStatement.{u, v, w} ∧
    HilbertSchmidtUniformEvaluationStatement.{u, v, w}

end Langlands.Analysis.OperatorIdeals
