import Langlands.Global.Arithmetic.CharacterPrescriptionProof
import Langlands.Global.Arithmetic.CMFiniteCharacterPrescriptionReductionProof
import Langlands.Global.Arithmetic.CMUnramifiedInfinityProof
import Langlands.Global.Arithmetic.IntegralUnitCharacterExtensionProof
import Langlands.Global.Arithmetic.CMCharacterAssemblyProof

/-! # The coherent CM-character globalization inputs -/

universe u v

namespace Langlands.Global

/-- The four CM-character prerequisites, with regular unit prescription
assembled from the first three proved inputs. -/
theorem cmCharacterGlobalization : CMCharacterGlobalizationStatement.{u, v} :=
  ⟨cmUnramifiedInfinityRealization.{u},
    cmFiniteCharacterPrescriptionOfFiniteOrder.{u} finiteOrderCharacterPrescription_proof.{u},
    integralUnitCharacterExtension.{u},
    cmRegularUnitPrescriptionOfInputs.{u, v} cmUnramifiedInfinityRealization.{u}
      (cmFiniteCharacterPrescriptionOfFiniteOrder.{u} finiteOrderCharacterPrescription_proof.{u})
      integralUnitCharacterExtension.{u}⟩

end Langlands.Global
