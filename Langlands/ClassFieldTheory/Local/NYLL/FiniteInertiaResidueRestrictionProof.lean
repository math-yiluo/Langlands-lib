import Langlands.ClassFieldTheory.Local.NYLL.RamifiedResidueStatement

/-! # Supplied residue actions commute with finite inertia restriction -/

namespace Langlands.LocalClassField.NYLL

universe u v

/-- The supplied residue inclusion intertwines the actual field restriction
with the supplied residue actions. -/
theorem finiteInertiaResidueRestriction :
    FiniteInertiaResidueRestrictionStatement.{u, v} := by
  intro p hp F E hFE hTower hAbelian TF TU TE σ y
  let := finiteInertiaPadicTower F E TF
  let := finiteInertiaField_isGalois F E TF
  obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
  change PadicField.TopologicalData.relativeResidueMap TU TE
      (TU.residue (Ramification.Padic.integerAutomorphism TU F.Carrier
        (finiteInertiaRestriction F E TF σ) z)) =
    TE.residue (Ramification.Padic.integerAutomorphism TE F.Carrier σ
      (PadicField.TopologicalData.relativeIntegerMap TU TE z))
  rw [PadicField.TopologicalData.relativeResidueMap_residue]
  apply congrArg TE.residue
  apply Subtype.ext
  exact finiteInertiaRestriction_apply F E TF σ (z : finiteInertiaField F E TF)

end Langlands.LocalClassField.NYLL
