import Langlands.GroupScheme.Rational.RelativeRankStatement
import Langlands.GroupScheme.Rational.RelativeSimpleRootBasis
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Proof of the actual simple relative-root basis -/

universe u

namespace Langlands.GroupScheme

/-- For a maximal split torus of an actual connected reductive group over any field
and a generic cocharacter, the actual simple relative roots are finite and form a
rational basis of the relative root span, whose dimension is their number. -/
theorem relativeSimpleRootBasis : RelativeSimpleRootBasisStatement.{u} :=
  relativeSimpleRootBasisStatement_of_relativeRootSystemStatement
    (relativeRootSystemStatement_of_rootRankOneFactorizationStatement rootRankOneFactorization)

end Langlands.GroupScheme
