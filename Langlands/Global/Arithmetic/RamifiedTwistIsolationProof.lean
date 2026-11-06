import Langlands.Global.Arithmetic.CharacterPrescriptionProof
import Langlands.Global.Arithmetic.LocalCharactersArbitrarilyRamifiedProof
import Langlands.Global.Arithmetic.RamifiedTwistIsolationReductionProof

/-! # Ramified twist isolation -/

universe u

namespace Langlands.Global

/-- Proved finite-order prescription and arbitrarily ramified local characters
discharge both premises of the twist-isolation reduction. -/
theorem ramifiedTwistIsolation : RamifiedTwistIsolationStatement.{u} :=
  ramifiedTwistIsolationOfInputs.{u} finiteOrderCharacterPrescription_proof.{u}
    localCharactersArbitrarilyRamified.{u}

end Langlands.Global
