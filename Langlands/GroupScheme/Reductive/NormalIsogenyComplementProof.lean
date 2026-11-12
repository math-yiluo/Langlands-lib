import Langlands.GroupScheme.Reductive.NormalIsogenyComplementGeneration
import Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction
import Langlands.GroupScheme.Reductive.RootGenerationReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.RootVectorLineProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof

/-! # Semisimple normal complements over an arbitrary field: proof -/

universe u

namespace Langlands.GroupScheme

/-- A prescribed smooth connected closed normal subgroup of a semisimple group
over an arbitrary field is semisimple and has a semisimple closed normal
complement, commuting with it on every test scheme, whose multiplication from
the semisimple product is a central isogeny. Every structural premise of the
published conditional assembly is discharged by a published proof. -/
theorem semisimpleNormalIsogenyComplement :
    SemisimpleNormalIsogenyComplementStatement.{u} :=
  semisimpleNormalIsogenyComplement_of_generation
    (semisimpleAlmostSimpleGeneration_of_rootLines normalReductiveCenter
      (semisimpleRootGenerationReduction rootRankOneFactorization
        (algClosedMaximalTorusCentralizer_fromQuotient
          dynamicCentralizerReductive solvableTorusQuotient))
      absoluteRootVectorLine maximalTorusConjugacy)

end Langlands.GroupScheme
