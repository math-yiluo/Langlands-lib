import Langlands.GroupScheme.Torus.SplittingAssembly
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.RingTheory.Coalgebra.SeparablyClosedGroupLikeSpanningProof

/-! # Splitting of tori over separably closed fields -/

noncomputable section

universe u

namespace Langlands.GroupScheme

/-- Over a separably closed field every torus is split. -/
theorem toriAreSplit_of_isSepClosed (k : Type u) [Field k] [IsSepClosed k] : ToriAreSplit k :=
  fun T hT => SplittingAssembly.isSplit_of_isSepClosed_of_prerequisites
    Langlands.CoalgebraDescent.separablyClosedGroupLikeSpanning T hT

end Langlands.GroupScheme
