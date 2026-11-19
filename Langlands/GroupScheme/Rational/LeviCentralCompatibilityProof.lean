import Langlands.GroupScheme.Rational.LeviCentralCompatibilityStatements
import Langlands.GroupScheme.Rational.LeviSplitComponentInclusionProof
import Langlands.GroupScheme.Rational.StandardLeviCharacterAnnihilatorProof

/-! # Split components of nested Levis and characters of standard Levis: the conjunction

Pairs the two published component proofs into a proof of
`LeviCentralCompatibilityStatements` (Renard V.3.6, V.3.13).
-/

namespace Langlands.GroupScheme

universe u

/-- `LeviCentralCompatibilityStatements`: the pair of the published proofs
`leviSplitComponentInclusion` and `standardLeviCharacterAnnihilator`. -/
theorem leviCentralCompatibility : LeviCentralCompatibilityStatements.{u} :=
  ⟨leviSplitComponentInclusion, standardLeviCharacterAnnihilator⟩

end Langlands.GroupScheme
