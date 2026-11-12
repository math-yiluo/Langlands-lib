import Langlands.GroupScheme.Rational.RelativeRankStatement
import Langlands.GroupScheme.Rational.RelativeRankIdentityProof
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasisProof

/-!
# Proof of `Langlands.GroupScheme.RelativeRankStatement`

A named theorem for a statement that follows directly from published results.
-/

universe u

namespace Langlands.GroupScheme

/-- Proof of `RelativeRankStatement`. -/
theorem relativeRank : RelativeRankStatement.{u} :=
  ⟨relativeSimpleRootBasis, relativeRankIdentity⟩

end Langlands.GroupScheme
