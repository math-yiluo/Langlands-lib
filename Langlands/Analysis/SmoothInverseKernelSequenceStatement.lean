import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

universe uV uG

namespace Langlands.Analysis

open MeasureTheory Filter
open scoped Topology Manifold ContDiff

/-- One sequence of smooth compact kernels has normalized inverse integral,
and both original and inverse topological supports concentrate at the identity. -/
def SmoothInverseKernelSequenceStatement : Prop :=
  ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [ChartedSpace V G] [IsManifold 𝓘(ℝ, V) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ],
    ∃ κ : ℕ → G → ℝ,
      (∀ n, ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℝ) ∞ (κ n) ∧
        HasCompactSupport (κ n) ∧ (∀ g, 0 ≤ κ n g) ∧ 0 < κ n 1 ∧
        Integrable (fun g => κ n g⁻¹) μ ∧ (∫ g, κ n g⁻¹ ∂μ) = 1) ∧
      ∀ U ∈ 𝓝 (1 : G), ∀ᶠ n in atTop,
        tsupport (κ n) ⊆ U ∧ tsupport (fun g => κ n g⁻¹) ⊆ U

end Langlands.Analysis
