import Mathlib.Geometry.Manifold.BumpFunction
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section

universe uV uG

namespace Langlands.Analysis

open MeasureTheory
open scoped Topology Manifold ContDiff

/-- Nonnegative smooth compact kernels with inverse integral one exist in
every identity neighborhood of the original finite-dimensional manifold group. -/
def SmoothNormalizedInverseKernelStatement : Prop :=
  ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V]
    (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [ChartedSpace V G] [IsManifold 𝓘(ℝ, V) ∞ G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [Measure.IsOpenPosMeasure μ]
    (U : Set G), U ∈ 𝓝 (1 : G) →
    ∃ κ : G → ℝ,
      ContMDiff 𝓘(ℝ, V) 𝓘(ℝ, ℝ) ∞ κ ∧
      HasCompactSupport κ ∧ tsupport κ ⊆ U ∧
      (∀ g, 0 ≤ κ g) ∧ 0 < κ 1 ∧
      Integrable (fun g => κ g⁻¹) μ ∧
      (∫ g, κ g⁻¹ ∂μ) = 1

end Langlands.Analysis
