import Langlands.Global.Arithmetic.CharacterPrescriptionProof
import Langlands.Global.Arithmetic.CMFiniteCharacterPrescriptionReductionProof
import Langlands.Global.Arithmetic.CMUnramifiedInfinityProof
import Langlands.Global.Arithmetic.IntegralUnitCharacterExtensionProof
import Langlands.Global.Arithmetic.CMCharacterAssemblyProof

/-! # Regular CM infinity type with prescribed unit components -/

universe u v

namespace Langlands.Global

/-- Proved unramified infinity realization, finite self-dual prescription and
integral-unit extension discharge the three premises of the CM assembly. -/
theorem cmRegularUnitPrescription : CMRegularUnitPrescriptionStatement.{u, v} :=
  cmRegularUnitPrescriptionOfInputs.{u, v} cmUnramifiedInfinityRealization.{u}
    (cmFiniteCharacterPrescriptionOfFiniteOrder.{u} finiteOrderCharacterPrescription_proof.{u})
    integralUnitCharacterExtension.{u}

end Langlands.Global
