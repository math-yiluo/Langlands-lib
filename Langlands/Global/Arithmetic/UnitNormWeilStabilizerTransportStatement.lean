import Langlands.Global.Arithmetic.AuxiliaryCharacterStatement
import Langlands.Global.Arithmetic.GeneralPositionStatement

noncomputable section

universe u

namespace Langlands.Global

open LocalFactor.CommonClosure GeneralPosition

/-- Transport the field-side exact unit-norm stabilizer through actual
norm and conjugation reciprocity squares in a common closure. -/
def UnitNormWeilStabilizerTransportStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : Extension F)
    (e : ReciprocityFamily F), NormalizedReciprocity F e →
    letI := (fieldData F E).topology
    ∀ χ : FieldCharacter F E,
      let M := galoisClosure F E
      let h := le_galoisClosure F E
      let L := IntermediateField.restrict h
      let a := Units.mapEquiv (IntermediateField.restrictAlgEquiv h).toMulEquiv
      let χL := χ.toMonoidHom.comp a.symm.toMonoidHom
      letI := (M.asPadicField (p := p)).canonicalNormedField
      HasExactUnitNormStabilizer L χL →
        HasExactWeilStabilizer F E (weilCharacter F e E χ)

end Langlands.Global
