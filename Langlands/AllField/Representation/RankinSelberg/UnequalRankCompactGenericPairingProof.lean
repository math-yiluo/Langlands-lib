import Langlands.Representation.RankinSelberg.UnequalRankCompactGenericPairingProof
import Langlands.AllField.Group.GL.CountabilityProof
import Langlands.AllField.Representation.RankinSelberg.UnequalRankCompactPairingMultiplicity
/-!
# Proof of the unequal-rank compact generic pairing statement

The covariant pairing space between the compact mirabolic model of rank `r + 1` and an
admissible irreducible generic representation of `GL_(n+1)` is a complex line for every
exponent. This combines the conditional result
`unequalRankCompactGenericPairing_of_multiplicityOne` with the Library proof of
Whittaker multiplicity one.
-/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding UnequalRankAnalyticStatement UnequalRankBilinearUniquenessStatement UnequalRankCommonGeneratorStatement UnequalRankCompactGenericPairingStatement UnequalRankFunctionalEquationStatement UnequalRankMirabolicPairingRigidityStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply unequalRankCompactGenericPairing
open Langlands.AllField.RankinSelberg

universe uF uW

/-- The unequal-rank compact generic pairing space has exact dimension one. -/
theorem unequalRankCompactGenericPairing 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n r : ℕ) :
    UnequalRankCompactGenericPairingStatement.{uF, uW} F T n r :=
  Langlands.AllField.RankinSelberg.UnequalRankCompactPairing.unequalRankCompactGenericPairing_of_multiplicityOne
    Whittaker.multiplicityOne.{uF, uW} F T n r

end Langlands.AllField.RankinSelberg
