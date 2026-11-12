import Langlands.GroupScheme.SimplyConnected.AlmostSimpleRationalGenerationReduction
import Langlands.GroupScheme.Reductive.NormalIsogenyComplementGeneration
import Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction
import Langlands.GroupScheme.Reductive.RootGenerationReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.RootVectorLineProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Rational generation of simply connected groups by almost-simple factors: proof -/

universe u

namespace Langlands.GroupScheme

/-- Over any field, the rational points of a simply connected group are generated
by the rational points of its closed normal almost-simple subgroups. -/
theorem simplyConnectedAlmostSimpleRationalGeneration :
    SimplyConnectedAlmostSimpleRationalGenerationStatement.{u} := by
  have hCentralizer : AlgClosedMaximalTorusCentralizerStatement.{u} :=
    algClosedMaximalTorusCentralizer_fromQuotient dynamicCentralizerReductive
      solvableTorusQuotient
  have hRoots : SemisimpleRootGenerationStatement.{u} :=
    semisimpleRootGenerationReduction rootRankOneFactorization hCentralizer
  have hGeneration : SemisimpleAlmostSimpleGenerationStatement.{u} :=
    semisimpleAlmostSimpleGeneration_of_rootLines normalReductiveCenter hRoots
      absoluteRootVectorLine maximalTorusConjugacy
  have hComplement : SemisimpleNormalIsogenyComplementStatement.{u} :=
    semisimpleNormalIsogenyComplement_of_generation hGeneration
  exact simplyConnectedAlmostSimpleRationalGeneration_of_normalIsogenyComplement hComplement

end Langlands.GroupScheme
