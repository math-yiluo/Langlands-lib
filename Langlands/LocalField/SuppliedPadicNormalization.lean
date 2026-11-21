import Langlands.LocalField.PadicBridge
import Langlands.AllField.HarmonicAnalysis.Conductor
import Langlands.HarmonicAnalysis.Conductor

/-! # The normalization of supplied p-adic topological data -/

namespace Langlands.PadicField.TopologicalData

open HarmonicAnalysis

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The p-adic realization and its underlying local-field data have the same
additive conductor, computed from the same valuation lattices. -/
theorem toLocalFieldData_additiveConductor :
    letI := T.topology
    ∀ ψ : UnitaryAdditiveCharacter F.Carrier,
      T.toLocalFieldData.additiveConductor ψ = T.additiveConductor ψ := by
  let := T.topology
  intro ψ
  exact le_antisymm
    ((T.additiveConductor_spec ψ).2 _ (T.toLocalFieldData.additiveConductor_spec ψ).1)
    ((T.toLocalFieldData.additiveConductor_spec ψ).2 _ (T.additiveConductor_spec ψ).1)

end Langlands.PadicField.TopologicalData
