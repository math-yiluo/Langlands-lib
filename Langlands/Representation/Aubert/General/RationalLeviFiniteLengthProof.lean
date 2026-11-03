import Langlands.Representation.Aubert.General.StandardLeviInductionFiniteLength
import Langlands.Representation.Aubert.General.StandardLeviJacquetFiniteLength
import Langlands.Representation.Aubert.General.RationalInvolutivityReduction

/-! # Finite length for the actual standard parabolics inside standard Levis -/

noncomputable section

universe u v

open AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

/-- Both inside-Levi finite-length preservation properties follow from the
ambient finite-length and topological premises of the published statement. -/
theorem rationalLeviFiniteLengthStatement :
    RationalLeviFiniteLengthStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hU hP hproj hUc hiFl hrFl hM J
  let _ := (hM J).locallyCompactSpace
  intro I
  exact ⟨standardLeviInduction_preservesFiniteLength.{u, v}
      i ν hInter hG hi hν hStandard hU hproj hUc hiFl J (hM J) I,
    standardLeviJacquet_preservesFiniteLength.{u, v}
      i ν hInter hG hi hν hStandard hU hproj hUc hiFl hrFl J (hM J) I⟩

end Langlands.Aubert.General.RationalPointFamily
