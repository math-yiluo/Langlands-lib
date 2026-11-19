import Langlands.LocalField.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.Valued.NormedValued

open scoped NNReal

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime]

/-- The nonnegative-real valuation associated to the base-extending spectral norm. -/
noncomputable def canonicalValuation (F : PadicField.{u} p) :
    Valuation F.Carrier ℝ≥0 := by
  exact LocalField.canonicalValuation (Padic p) F.Carrier

/-- The valuative comparison induced by the spectral valuation. -/
@[instance_reducible]
noncomputable def canonicalValuativeRel (F : PadicField.{u} p) :
    ValuativeRel F.Carrier :=
  ValuativeRel.ofValuation F.canonicalValuation

/-- The canonical local-field realization of every finite extension of `Padic p`. -/
noncomputable def canonicalTopologicalData (F : PadicField.{u} p) :
    F.TopologicalData := by
  apply TopologicalData.ofLocalData
  apply LocalField.canonicalTopologicalData (Padic p) F.Carrier
  intro a b
  change ‖a‖ ≤ ‖b‖ ↔ Padic.mulValuation a ≤ Padic.mulValuation b
  simp only [← not_lt, Padic.norm_lt_norm_iff_mulValuation_lt]

end Langlands.PadicField
