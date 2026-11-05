import Mathlib.Topology.UrysohnsLemma
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

noncomputable section

namespace Langlands.Analysis

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe uG

/-- A normalized nonnegative continuous Hermitian weight in each identity neighborhood. -/
def HermitianNeighborhoodWeightStatement : Prop :=
  ∀ {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [IsFiniteMeasureOnCompacts μ] [IsOpenPosMeasure μ]
    (d : G →* ℝ≥0), Continuous d →
    ∀ (U : Set G), U ∈ nhds (1 : G) →
      ∃ f : G → ℝ, Continuous f ∧ HasCompactSupport f ∧ tsupport f ⊆ U ∧
        (∀ g, 0 ≤ f g) ∧ Integrable f μ ∧ (∫ g, f g ∂μ) = 1 ∧
        ∀ g, f g = (d g : ℝ) * f g⁻¹

end Langlands.Analysis
