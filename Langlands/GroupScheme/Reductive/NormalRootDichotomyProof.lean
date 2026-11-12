import Langlands.GroupScheme.Reductive.NormalRootDichotomyReduction
import Langlands.GroupScheme.Reductive.NormalCenterProof
import Langlands.GroupScheme.Reductive.RootGenerationReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof
import Langlands.GroupScheme.Absolute.RootVectorLineProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof

/-! # semisimpleNormalRootDichotomy: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- For a smooth connected normal closed subgroup of a semisimple group over an algebraically closed field, each actual root subgroup of the specified split maximal torus is contained in that subgroup or centralizes it on every test and refinement. -/
theorem semisimpleNormalRootDichotomy :
    SemisimpleNormalRootDichotomyStatement.{u} :=
  semisimpleNormalRootDichotomy_of_rootLines normalReductiveCenter
    (semisimpleRootGenerationReduction rootRankOneFactorization
      (algClosedMaximalTorusCentralizerReduction dynamicCentralizerReductive
        noTorusUnipotent solvableTorusQuotient))
    absoluteRootVectorLine maximalTorusConjugacy

end Langlands.GroupScheme
