import Langlands.GroupScheme.FlagCoreAssembly
import Langlands.GroupScheme.Absolute.BorelProperQuotientProof
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.MaximalTorusConjugacyProof
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.SolvableProperFixedPointProof

/-! # flagCoreDualLine: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- Under the exact flag-core hypotheses over an algebraically closed field, every rational orbit vector admits a nonvanishing linear form whose line is stable under the rational points of the specified subgroup. -/
theorem flagCoreDualLine :
    FlagCoreDualLineStatement.{u} :=
  FlagCore.flagCoreDualLine_of_prerequisites someBorelQuotientProper borelConjugacy
    maximalTorusConjugacy torusFiniteGaloisSplitting solvableProperFixedPoint

end Langlands.GroupScheme
