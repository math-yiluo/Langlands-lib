import Langlands.Global.Arithmetic.AlmostEverywherePowerHalfProof
import Langlands.Global.Arithmetic.CharacterPrescriptionReduction

/-! # Finite-order Hecke-character prescription with doubled exponent -/

universe u

namespace Langlands.Global

/-- The actual idele classes admit the finite quotient needed for prescription,
using the proved almost-everywhere half-power descent. -/
theorem prescriptionFiniteQuotient_proof : PrescriptionFiniteQuotientStatement.{u} :=
  prescriptionFiniteQuotient_of_halfPower almostEverywherePowerHalfStatement

/-- **Grunwald–Wang finite-order prescription.** Continuous finite-order local
characters, including the whole infinite factor, extend to an actual Hecke
character killed by twice their given common exponent. -/
theorem finiteOrderCharacterPrescription_proof :
    FiniteOrderCharacterPrescriptionStatement.{u} :=
  finiteOrderCharacterPrescription_of_finiteQuotient prescriptionFiniteQuotient_proof

end Langlands.Global
