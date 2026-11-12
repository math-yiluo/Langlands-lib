import Langlands.GroupScheme.Rational.RelativeRankReduction
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementProof
import Langlands.GroupScheme.Rational.CharacterRestrictionProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusConjugacyProof

/-! # Intrinsic split-rank and rational-character rank identities -/

universe u

namespace Langlands.GroupScheme

/-- **Intrinsic rank identities.** Over every field, for every actual maximal split torus
of a connected reductive group, the split rank equals the full split-torus rank, which is
the relative root rank plus the rational-character rank, and rationalized restriction of
characters to every actual split component is bijective. -/
theorem relativeRankIdentity : RelativeRankIdentityStatement.{u} :=
  relativeRankIdentityStatement_of_complement_restriction_conjugacy
    relativeCharacterRootComplement characterRestriction maximalSplitTorusConjugacy

end Langlands.GroupScheme
