import Langlands.GroupScheme.Reductive.SemisimpleNormalComplementConstruction
import Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction
import Langlands.GroupScheme.Reductive.RootGenerationReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Absolute.RootVectorLineProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # Commuting normal complements in semisimple groups: proof -/

universe u

namespace Langlands.GroupScheme

/-- A smooth connected closed normal subgroup of a semisimple group over an
algebraically closed field has a closed normal complement commuting with it on
every test scheme, with flat surjective multiplication. -/
theorem semisimpleNormalComplement : SemisimpleNormalComplementStatement.{u} :=
  semisimpleNormalComplement_of_almostSimpleGeneration
    (semisimpleAlmostSimpleGeneration_of_rootLines normalReductiveCenter
      (semisimpleRootGenerationReduction rootRankOneFactorization
        (algClosedMaximalTorusCentralizer_fromQuotient
          dynamicCentralizerReductive solvableTorusQuotient))
      absoluteRootVectorLine maximalTorusConjugacy)

end Langlands.GroupScheme
