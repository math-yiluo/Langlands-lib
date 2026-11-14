import Langlands.Representation.Aubert.General.RationalDetectionFiniteLengthReductionStatements
import Langlands.Representation.Aubert.General.SupportCategoryReductions
import Langlands.Representation.Aubert.General.RationalIrreducibleJacquetFactorDetection
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity

/-! # Zero detection on the actual rational-point support categories -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The full rational zero-detection target follows from the full rational
irreducible Jacquet detection proposition. Compact-limit of every standard
unipotent subgroup is proved from the displayed `hStandard`. This theorem does
not prove the detection premise. -/
theorem rationalSupportCategoryZeroDetection_of_irreducibleJacquetDetection
    (hdet : RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v}) :
    RationalSupportCategoryZeroDetectionStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  exact supportCategoryZeroDetection_of_irreducibleJacquetDetection
    (fun J =>
      standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν J)
    (hdet k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)

/-- The full rational zero-detection target follows from the full rational
cuspidal Jacquet-factor extraction proposition, through the published
conditional irreducible detection theorem. This theorem does not prove the
extraction premise. -/
theorem rationalSupportCategoryZeroDetection_of_cuspidalFactors
    (hextract : RationalCuspidalJacquetFactorExtractionStatement.{u, v}) :
    RationalSupportCategoryZeroDetectionStatement.{u, v} :=
  rationalSupportCategoryZeroDetection_of_irreducibleJacquetDetection
    (rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors hextract)

/-- The published reduction statement of zero detection to cuspidal
Jacquet-factor extraction. -/
theorem rationalSupportCategoryZeroDetectionReduction :
    RationalSupportCategoryZeroDetectionReductionStatement.{u, v} :=
  fun hextract => rationalSupportCategoryZeroDetection_of_cuspidalFactors hextract

end Langlands.Aubert.General.RationalPointFamily
