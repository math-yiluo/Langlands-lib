import Langlands.GroupScheme.SimplyConnected.SplitTorusCentralizerDerivedCorootComparisonReduction
import Langlands.GroupScheme.Reductive.RootDatumExistence
import Langlands.GroupScheme.Dynamic.CentralizerReductiveProof

/-! # Actual coroot comparison for derived split-torus centralizers -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Over every algebraically closed field, the integral coroot lattice of the
actual derived subgroup of a split-torus centralizer maps onto the span of a
subset of simple coroots of the ambient connected reductive group, for actual
compatible split maximal tori and their finite reduced root data. -/
theorem splitTorusCentralizerDerivedCorootComparison :
    SplitTorusCentralizerDerivedCorootComparisonStatement.{u} :=
  splitTorusCentralizerDerivedCorootComparison_of_rootDatumExistence
    rootDatumExistence dynamicCentralizerReductive

end Langlands.GroupScheme
