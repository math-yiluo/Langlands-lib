import Langlands.Representation.RankinSelberg.UnequalRankCompactPairingMultiplicity
import Langlands.Representation.Whittaker.MultiplicityOneProof

/-!
# Proof of the unequal-rank compact generic pairing statement

The covariant pairing space between the compact mirabolic model of rank `r + 1` and an
admissible irreducible generic representation of `GL_(n+1)` is a complex line for every
exponent. This combines the conditional result
`unequalRankCompactGenericPairing_of_multiplicityOne` with the Library proof of
Whittaker multiplicity one.
-/

namespace Langlands.RankinSelberg

universe uF uW

/-- The unequal-rank compact generic pairing space has exact dimension one. -/
theorem unequalRankCompactGenericPairing {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n r : ℕ) :
    UnequalRankCompactGenericPairingStatement.{uF, uW} F T n r :=
  UnequalRankCompactPairing.unequalRankCompactGenericPairing_of_multiplicityOne
    Whittaker.multiplicityOne.{uF, uW} F T n r

end Langlands.RankinSelberg
