import Langlands.GroupScheme.Rational.RootReflectionExistenceStatement
import Langlands.GroupScheme.Rational.RootGeneratedCentralizerReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Proof of intrinsic integral relative-root reflection existence -/

universe u

namespace Langlands.GroupScheme

/-- Every actual relative root of a maximal split torus in a connected reductive
group over an arbitrary field has integral reflection data whose rational
representative centralizes the full scheme-theoretic kernel of the root. -/
theorem relativeRootReflectionExistence : RelativeRootReflectionExistenceStatement.{u} :=
  relativeRootReflectionExistence_of_rootRankOneFactorization rootRankOneFactorization

end Langlands.GroupScheme
