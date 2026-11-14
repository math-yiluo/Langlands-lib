import Langlands.Representation.Aubert.General.RationalDetectionFiniteLengthReductionStatements
import Langlands.Representation.Aubert.General.RationalSharpConsequenceTargets
import Langlands.Representation.Aubert.General.RationalStandardFiniteLength
import Langlands.Representation.Aubert.General.SharpFiniteLength

/-! # Finite length of the actual rational terminal cokernel from dynamic finite length -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme

/-- The two dynamic finite-length statements (Renard VI.6.2 and VI.6.4) at the
carrier universe `max (u + 1) v` give finite length of the actual terminal
cokernel `E#` on the actual standard rational-point families. -/
theorem rationalSharpFiniteLengthStatement_of_dynamic
    (hiD : DynamicInductionFiniteLengthStatement.{u, max (u + 1) v})
    (hr : DynamicJacquetFiniteLengthStatement.{u, max (u + 1) v}) :
    RationalSharpFiniteLengthStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hOrder hRoots hU hUc
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _
  exact sharpFiniteLengthTarget_of_inductionJacquet _ _ _ _ _ _ _ _
    (fun J => standardInductionJacquet_preservesFiniteLength_of_dynamic
      i ν hStandard hG hi hν hU hiD hr J)

/-- The published reduction statement of Sharp finite length to the two
dynamic finite-length targets. -/
theorem rationalSharpFiniteLengthReduction : RationalSharpFiniteLengthReductionStatement.{u, v} :=
  fun hiD hr => rationalSharpFiniteLengthStatement_of_dynamic hiD hr

end Langlands.Aubert.General.RationalPointFamily
