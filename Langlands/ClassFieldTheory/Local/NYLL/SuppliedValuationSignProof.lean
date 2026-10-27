import Langlands.ClassFieldTheory.Local.NYLL.SuppliedValuationSignStatement

/-! # Valuation sign compatibility for arbitrary supplied local-field data -/

namespace Langlands.LocalClassField.NYLL

universe u

/-- NYLL's valuation map on units is the negative of the supplied additive order. -/
theorem suppliedValuationSign : SuppliedValuationSignStatement.{u} := by
  intro p _ F T a
  rw [PadicField.TopologicalData.ord, neg_neg]
  exact WithZero.logEquiv_apply _

end Langlands.LocalClassField.NYLL
