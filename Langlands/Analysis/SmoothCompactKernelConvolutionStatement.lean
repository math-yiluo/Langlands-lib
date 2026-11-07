import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

universe uV uG uE

namespace Langlands.Analysis

open MeasureTheory
open scoped Manifold ContDiff

/-- A smooth compact scalar kernel smooths a continuous Banach-valued function
by the literal group convolution, for any measure finite on compact sets. -/
def SmoothCompactKernelConvolutionStatement : Prop :=
  ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [ChartedSpace V G]
    [LieGroup 𝓘(ℝ, V) ∞ G] [MeasurableSpace G] [BorelSpace G]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ]
    (w : C(G, E)) (κ : G → ℂ),
    ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℂ) ∞ κ → HasCompactSupport κ →
    (∀ p : G, Integrable (fun y => κ (y⁻¹ * p) • w y) μ) ∧
      ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, E) ∞
        (fun p : G => ∫ y, κ (y⁻¹ * p) • w y ∂μ)

end Langlands.Analysis
