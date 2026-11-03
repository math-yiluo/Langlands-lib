import Langlands.Representation.Aubert.General.RationalJacquetGeometricExpansion
import Langlands.Representation.Aubert.General.RationalSuppliedCoxeterComparisons

/-! # Rational Jacquet compatibility from the rational geometric expansion -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

/-- The complete rational geometric expansion implies the complete published
Jacquet compatibility proposition, with no additional structural premise. -/
def RationalJacquetGeometricAssemblyStatement : Prop :=
  RationalGeometricK0ExpansionStatement.{u, v} →
    RationalJacquetCompatibilityStatement.{u, v}

/-- The rational geometric expansion supplies every literal intersection row.
The standard-Levi Weyl identification is derived for the original supplied
Coxeter system, rather than imposed as another premise. -/
theorem rationalIntersectionExpansions_of_rationalGeometricK0Expansion
    (hExpansion : RationalGeometricK0ExpansionStatement.{u, v}) :
    RationalIntersectionExpansionStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let _ := hG.isAffineHom
  let _ := hi.isSplitSubtorus.mono
  let _ : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hRoots hInter hU hP hproj hUc hiFl hrFl
    hM hLproj hLUc hiLFl hrLFl
  let _ := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ hConj hN hZ CM cs hLength hSimple _ _
  dsimp only
  intro J
  let flL := fun A => standardLeviParabolicFiniteLength.{u, v}
    i ν hInter hG hi hν hU hP A (hM A)
    (hLproj A) (hLUc A) (hiLFl A) (hrLFl A)
  have hIdent := actualLeviWeylIdentification_of_rootLength
    i ν hN hZ cs hG hi hRoots hν hLength
  have hPoint := rationalPointGeometricExpansion_of_rationalGeometricK0Expansion.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hInter hStandard
    hU hM flL hExpansion hRoots hP hproj hUc hiFl hrFl hIdent
  exact rationalIntersectionExpansion_of_pointGeometricExpansion.{u, v}
    i ν hN hZ cs hLength hSimple hG hi hν hConj hInter hStandard hU hM
    (standardParabolicFiniteLength.{u, v}
      i ν hStandard hG hi hν hU hP hproj hUc hiFl hrFl)
    flL hPoint J

/-- The sole additional premise is the rational geometric expansion at its
complete universe scope. All other inputs are those already displayed in the
published Jacquet target. -/
theorem rationalJacquetCompatibility_of_rationalGeometricK0Expansion
    (hExpansion : RationalGeometricK0ExpansionStatement.{u, v}) :
    RationalJacquetCompatibilityStatement.{u, v} :=
  rationalJacquetCompatibility_of_intersectionExpansions.{u, v}
    (rationalIntersectionExpansions_of_rationalGeometricK0Expansion.{u, v} hExpansion)

end Langlands.Aubert.General.RationalPointFamily
