import Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Reductive.RootGenerationReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.RootVectorLineProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof

/-! # Generation of semisimple groups by normal almost-simple subgroups: proof -/

universe u

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a closed subgroup of a semisimple
group containing every closed normal almost-simple subgroup has full range
on all test schemes. Every structural premise of the published conditional
assembly is discharged by a published proof. -/
theorem semisimpleAlmostSimpleGeneration :
    SemisimpleAlmostSimpleGenerationStatement.{u} :=
  semisimpleAlmostSimpleGeneration_of_rootLines normalReductiveCenter
    (semisimpleRootGenerationReduction rootRankOneFactorization
      (algClosedMaximalTorusCentralizer_fromQuotient
        dynamicCentralizerReductive solvableTorusQuotient))
    absoluteRootVectorLine maximalTorusConjugacy

end Langlands.GroupScheme
