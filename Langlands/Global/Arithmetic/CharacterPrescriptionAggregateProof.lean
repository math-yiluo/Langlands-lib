import Langlands.Global.Arithmetic.CharacterPrescriptionProof
import Langlands.Global.Arithmetic.LocalCharactersArbitrarilyRamifiedProof
import Langlands.Global.Arithmetic.RamifiedTwistIsolationReductionProof

/-! # The coherent finite-character prescription inputs -/

universe u

namespace Langlands.Global

/-- Finite-order prescription, arbitrarily ramified local characters, and the
twist isolation obtained from those two results. -/
theorem characterPrescription : CharacterPrescriptionStatement.{u} :=
  ⟨finiteOrderCharacterPrescription_proof.{u}, localCharactersArbitrarilyRamified.{u},
    ramifiedTwistIsolationOfInputs.{u} finiteOrderCharacterPrescription_proof.{u}
      localCharactersArbitrarilyRamified.{u}⟩

end Langlands.Global
