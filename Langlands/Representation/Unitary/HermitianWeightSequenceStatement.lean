import Langlands.Representation.Unitary.HermitianNeighborhoodWeightStatement
import Mathlib.Order.Filter.CountablyGenerated
import Mathlib.Order.Filter.AtTopBot.Basic

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure Filter
open scoped NNReal Topology

universe uG

/-- A countable local base gives normalized continuous Hermitian weights whose
topological supports shrink into every identity neighborhood. -/
def HermitianWeightSequenceStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsCountablyGenerated (𝓝 (1 : G))]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ]
    (d : G →* ℝ≥0), Continuous d →
      ∃ f : ℕ → G → ℝ,
        (∀ n, Continuous (f n) ∧ HasCompactSupport (f n) ∧
          (∀ g, 0 ≤ f n g) ∧ Integrable (f n) μ ∧
          (∫ g, f n g ∂μ) = 1 ∧ ∀ g, f n g = (d g : ℝ) * f n g⁻¹) ∧
        ∀ U ∈ 𝓝 (1 : G), ∀ᶠ n in atTop, tsupport (f n) ⊆ U

end Langlands.Analysis
