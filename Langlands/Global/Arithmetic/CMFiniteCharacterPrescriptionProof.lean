import Langlands.Global.Arithmetic.CharacterPrescriptionProof
import Langlands.Global.Arithmetic.CMFiniteCharacterPrescriptionReductionProof

/-! # Conjugate-self-dual finite-order prescription on CM fields -/

universe u

namespace Langlands.Global

/-- Proved finite-order prescription discharges the premise of the CM
finite-prescription reduction. -/
theorem cmFiniteCharacterPrescription : CMFiniteCharacterPrescriptionStatement.{u} :=
  cmFiniteCharacterPrescriptionOfFiniteOrder.{u} finiteOrderCharacterPrescription_proof.{u}

end Langlands.Global
