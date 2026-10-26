import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence.Definitions
import Langlands.LocalField.Normalization.Definitions

/-! # Valuation sign compatibility for supplied local-field data -/

namespace Langlands.LocalClassField.NYLL

universe u

/-- NYLL's valuation map on units is the negative of the supplied additive order. -/
def SuppliedValuationSignStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData)
    (a : F.Carrierˣ),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap
      F.Carrier (Additive.ofMul a) = -T.ord (a : F.Carrier)

end Langlands.LocalClassField.NYLL
