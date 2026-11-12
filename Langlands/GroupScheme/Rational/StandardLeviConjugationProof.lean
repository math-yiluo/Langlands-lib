import Langlands.GroupScheme.Rational.StandardLeviConjugationAssembly
import Langlands.GroupScheme.Rational.RootSystemFromFactorPairs
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof

/-! # Proof of general standard-Levi conjugation and lift independence -/

universe u

namespace Langlands.GroupScheme

/-- **Standard-Levi conjugation and normalizer-lift independence** over
arbitrary fields, for connected reductive groups, actual maximal split tori and
generic cocharacters. -/
theorem standardLeviConjugation : StandardLeviConjugationStatement.{u} :=
  standardLeviConjugationStatement_of_relativeRootSystemStatement
    (relativeRootSystemStatement_of_rootRankOneFactorizationStatement
      rootRankOneFactorization.{u})

end Langlands.GroupScheme
