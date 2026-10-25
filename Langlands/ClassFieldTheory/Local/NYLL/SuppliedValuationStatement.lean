import Langlands.LocalField.RelativeIntegers
import Mathlib.RingTheory.Valuation.Extension

/-! # Relative valuation compatibility for supplied local-field data -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- The supplied valuation on an extension field extends the supplied valuation
on its base, along the actual compatible field algebra map. -/
def SuppliedRelativeValuationExtensionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    (TF : F.TopologicalData) (TE : E.TopologicalData),
    letI := TF.valuativeRel
    letI := TE.valuativeRel
    Valuation.HasExtension (ValuativeRel.valuation F.Carrier)
      (ValuativeRel.valuation E.Carrier)

end Langlands.LocalClassField.NYLL
