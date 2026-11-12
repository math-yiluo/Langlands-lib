import Langlands.GroupScheme.Reductive.RootPinningFromSplitTorus
import Langlands.GroupScheme.Reductive.RootDatumExistence

/-! # splitPinningExistence: unconditional proof from published reductions -/

universe u

namespace Langlands.GroupScheme

/-- A connected reductive field group with a supplied split maximal torus admits a SplitPinning, including a finite reduced root datum, a base and actual simple-root Lie trivializations. -/
theorem splitPinningExistence :
    SplitPinningExistenceStatement.{u} :=
  splitPinningExistence_of_rootDatumExistence rootDatumExistence

end Langlands.GroupScheme
