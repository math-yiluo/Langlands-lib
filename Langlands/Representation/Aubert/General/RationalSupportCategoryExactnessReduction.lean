import Langlands.Representation.Aubert.General.RationalDetectionFiniteLengthReductionStatements
import Langlands.Representation.Aubert.General.SupportCategoryExactnessReduction
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity

/-! # Conditional exactness detection for the actual rational-point families -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Aubert.General.RationalPointFamily

/-- The exact rational zero-detection proposition implies the exact rational
exactness-detection proposition, with compact-limit proved from the displayed
standard-cocharacter data. -/
theorem rationalSupportCategoryExactnessDetection_of_zeroDetection
    (hdet : RationalSupportCategoryZeroDetectionStatement.{u, v}) :
    RationalSupportCategoryExactnessDetectionStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let _ := GroupScheme.simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  exact ExactnessDetection.supportCategoryExactnessDetection_of_zeroDetection
    (fun J =>
      standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν J)
    (hdet k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)

/-- The published reduction statement of exactness detection to zero
detection. -/
theorem rationalSupportCategoryExactnessDetectionReduction : RationalSupportCategoryExactnessDetectionReductionStatement.{u, v} :=
  fun hdet => rationalSupportCategoryExactnessDetection_of_zeroDetection hdet

end Langlands.Aubert.General.RationalPointFamily
