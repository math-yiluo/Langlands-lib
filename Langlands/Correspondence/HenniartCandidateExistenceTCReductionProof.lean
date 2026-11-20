import Langlands.Correspondence.HenniartCandidateExistenceExactStabilizerTCReductionProof

/-!
# Henniart's candidate existence from the totally complex inputs

The published exact-stabilizer reduction applies because Harris's Proposition 4.8
implies its exact-stabilizer form.
-/

namespace Langlands.Henniart

universe uK uW uP uE uQ

/-- The totally complex global inputs and local relative class formation give a
candidate at each finite quotient of the absolute Galois group of a p-adic field. -/
theorem candidateExistenceTCReduction :
    CandidateExistenceTCReductionStatement.{uK, uW, uP, uE, uQ} :=
  candidateExistenceTCReductionStatement_of_exactStabilizer.{uK, uW, uP, uE, uQ}
    candidateExistenceExactStabilizerTCReduction.{uK, uW, uP, uE, uQ}

end Langlands.Henniart
