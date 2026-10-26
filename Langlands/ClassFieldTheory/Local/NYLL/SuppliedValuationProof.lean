import Langlands.ClassFieldTheory.Local.NYLL.SuppliedValuationStatement

/-! # Relative valuation extension for arbitrary supplied local-field data -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- The supplied extension valuation extends the supplied base valuation along
the given compatible field algebra map. -/
theorem suppliedRelativeValuationExtension :
    SuppliedRelativeValuationExtensionStatement.{u, v} := by
  intro p _ F E _ _ TF TE
  let := TF.valuativeRel
  let := TE.valuativeRel
  constructor
  apply Valuation.isEquiv_iff_val_le_one.mpr
  intro x
  simpa only [PadicField.TopologicalData.Integers, Valuation.mem_integer_iff,
    Valuation.comap_apply] using
    (PadicField.TopologicalData.relative_mem_integers_iff TF TE x).symm

end Langlands.LocalClassField.NYLL
