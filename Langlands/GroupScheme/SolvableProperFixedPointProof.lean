import Langlands.GroupScheme.SolvableProperFixedPointStatement
import Langlands.GroupScheme.AlgebraicallyClosedSplitSolvableProof
import Langlands.GroupScheme.SplitSolvableFixedPointProof
import Langlands.GroupScheme.ProperPseudoComplete
import Langlands.GroupScheme.SchemeActionRationalPoints

/-! # Fixed points of solvable groups on proper schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every action of a smooth connected affine solvable group over an
algebraically closed field on a nonempty proper scheme fixes a rational point
on every relative scheme test and refinement. -/
theorem solvableProperFixedPoint :
    SolvableProperFixedPointStatement.{u} := by
  intro k _ _ H _ _ hConnected hSolvable X hProper hNonempty a
  let := hProper
  let := hNonempty
  exact splitSolvablePseudoCompleteFixedPoint k H
    (algebraicallyClosedSplitSolvable k H hConnected hSolvable) X
    (isPseudoComplete_of_isProper X) (nonempty_rationalPoints X) a

end Langlands.GroupScheme
