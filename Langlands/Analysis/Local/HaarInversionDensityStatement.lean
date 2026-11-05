import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Measure.WithDensity

noncomputable section

namespace Langlands.Haar

open MeasureTheory MeasureTheory.Measure
open scoped NNReal ENNReal

universe uG

/-- Actual inversion densities for left Haar and its inverse right Haar. -/
def HaarInversionDensityStatement : Prop :=
  ∀ (G : Type uG) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [IsHaarMeasure μ],
    μ.inv = μ.withDensity (fun g => (modularCharacter g : ℝ≥0∞)) ∧
      μ = μ.inv.withDensity (fun g => (modularCharacter g⁻¹ : ℝ≥0∞))

end Langlands.Haar
