import Langlands.GroupScheme.Reductive.RootGenerationReduction
import Langlands.GroupScheme.Rational.RootRankOneFactorizationProof
import Langlands.GroupScheme.Absolute.AlgClosedMaximalTorusCentralizerAssembly
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof
import Langlands.GroupScheme.Torus.NoTorusUnipotent
import Langlands.GroupScheme.Absolute.SolvableTorusQuotientProof

/-! # semisimpleRootGeneration: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Over an algebraically closed field, a closed subgroup containing every actual root subgroup for the specified split maximal torus of a semisimple group has full range on all test schemes. -/
theorem semisimpleRootGeneration :
    SemisimpleRootGenerationStatement.{u} :=
  semisimpleRootGenerationReduction rootRankOneFactorization
    (algClosedMaximalTorusCentralizerReduction dynamicCentralizerReductive
      noTorusUnipotent solvableTorusQuotient)

end Langlands.GroupScheme
