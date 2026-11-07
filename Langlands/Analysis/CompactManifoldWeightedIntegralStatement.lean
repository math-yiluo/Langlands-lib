import Langlands.Analysis.CompactParameterSmoothness
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

universe uX uV uM uH uN uE

namespace Langlands.Analysis

open MeasureTheory
open scoped Manifold ContDiff

/-- A jointly smooth scalar kernel on two real manifolds can be integrated
against a fixed continuous Banach-valued weight on a compact Hausdorff source. -/
def CompactManifoldWeightedIntegralStatement : Prop :=
  ∀ (X : Type uX) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (M : Type uM) [TopologicalSpace M] [ChartedSpace V M]
    [IsManifold 𝓘(ℝ, V) ∞ M]
    (H : Type uH) [NormedAddCommGroup H] [NormedSpace ℝ H]
    (N : Type uN) [TopologicalSpace N] [ChartedSpace H N]
    [IsManifold 𝓘(ℝ, H) ∞ N]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure X) [IsFiniteMeasure μ]
    (w : C(X, E)) (j : C(X, N)) (h : M × N → ℂ),
    ContMDiff (𝓘(ℝ, V).prod 𝓘(ℝ, H)) 𝓘(ℝ, ℂ) ∞ h →
    (∀ p : M, Integrable (fun x => h (p, j x) • w x) μ) ∧
      ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞
        (fun p : M => ∫ x, h (p, j x) • w x ∂μ)

end Langlands.Analysis
