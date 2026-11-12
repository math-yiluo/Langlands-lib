import Langlands.Representation.Smooth.RenardAdmissibleBidualProof
import Langlands.Representation.Smooth.RenardSigmaCompactSchurProof
import Langlands.Representation.Smooth.RenardInvariantPairingProof
import Langlands.Representation.Smooth.RenardCentralCharacterProof
import Langlands.Representation.Smooth.RenardHeckeCompletenessProof

/-! # Renard III.1.7–III.1.11 -/

universe u v w

namespace Langlands.Renard.Smooth

/-- The exact five-part aggregate of admissible biduality, sigma-compact Schur,
invariant pairings, central characters and Hecke completeness. -/
theorem renardSchurStatements : RenardSchurStatements.{u, v, w} :=
  ⟨admissibleBidual, sigmaCompactSchur, invariantContragredientPairing,
    centralCharacter, heckeCompleteness⟩

end Langlands.Renard.Smooth
