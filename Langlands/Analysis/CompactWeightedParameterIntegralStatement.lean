import Langlands.Analysis.CompactParameterSmoothness
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

universe uX uV uH uE

namespace Langlands.Analysis

open MeasureTheory Set
open scoped ContDiff

/-- Compact scalar kernels can be integrated against a continuous Banach-valued
weight while retaining smooth dependence on the parameter. -/
def CompactWeightedParameterIntegralStatement : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ]
    (w : C(X, E)) (j : C(X, H))
    (s : Set V) (_hs : IsOpen s) (t : Set H) (_ht : IsOpen t)
    (_hj : ∀ x, j x ∈ t)
    (h : V × H → ℂ) (_hh : ContDiffOn ℝ ∞ h (s ×ˢ t)),
    (∀ p ∈ s, Integrable (fun x => h (p, j x) • w x) μ) ∧
      ContDiffOn ℝ ∞ (fun p => ∫ x, h (p, j x) • w x ∂μ) s

end Langlands.Analysis
