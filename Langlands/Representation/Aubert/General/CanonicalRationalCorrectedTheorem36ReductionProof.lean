import Langlands.Representation.Aubert.General.CanonicalRationalComplexReductionStatements
import Langlands.Representation.Aubert.General.CanonicalRationalComplexTargets
import Langlands.Representation.Aubert.General.RationalCorrectedExactnessReduction
import Langlands.Representation.Aubert.General.RationalSupportCategoryDecompositionFromWhole
import Langlands.Representation.Aubert.General.SupportCategoryInductionJacquetReduction
import Langlands.Representation.Aubert.General.RationalCorrectedGradedTransitionProof
import Langlands.Representation.Aubert.General.SupportCategoryReductions
import Langlands.Representation.Aubert.General.SupportCategoryExactnessReduction
import Langlands.Representation.Aubert.General.RationalIrreducibleJacquetFactorDetection
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.CuspidalSupport.RationalCuspidalInducedEmbeddingFromWhole
import Langlands.GroupScheme.Rational.RationalBruhatProof

/-! # Proof of the reduction of canonical corrected Theorem 3.6 -/

noncomputable section


universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- Renard VI.3.5 at carrier universe `max (u + 1) v` and corrected graded
vanishing imply corrected Theorem 3.6 for the canonical actual complex. -/
theorem canonicalRationalCorrectedTheorem36Reduction :
    CanonicalRationalCorrectedTheorem36ReductionStatement.{u, v} := by
  intro hwhole hvan
  -- Step 1: cuspidal Jacquet-factor extraction from Renard VI.3.5.
  have hextract : RationalCuspidalJacquetFactorExtractionStatement.{u, v} :=
    rationalCuspidalJacquetFactorExtraction_of_inputs.{u, v}
      (rationalCuspidalExtractionInputs_of_wholeStatement.{u, v} hwhole)
  -- Step 2: support association.
  have hassoc : RationalCuspidalSupportAssociationStatement.{u, v} :=
    rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction.{u, v} hextract
  -- Step 3: induction-Jacquet stability of the support categories.
  have hind : RationalSupportCategoryInductionJacquetStatement.{u, v} :=
    rationalSupportCategoryInductionJacquet_of_decomposition_splitting_and_association.{u, v}
      (rationalSupportCategoryDecomposition_of_wholeStatement.{u, v} hwhole)
      (rationalLeviJacquetCuspidalRemainderSplitting_of_wholeStatement.{u, max (u + 1) v}
        hwhole)
      hassoc
  -- Step 4a: zero detection, through irreducible Jacquet detection.
  have hzero : RationalSupportCategoryZeroDetectionStatement.{u, v} := by
    have hirr : RationalSupportCategoryIrreducibleJacquetDetectionStatement.{u, v} :=
      rationalSupportCategoryIrreducibleJacquetDetection_of_cuspidalFactors.{u, v} hextract
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
      (hirr k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)
  -- Step 4b: exactness detection from zero detection.
  have hdet : RationalSupportCategoryExactnessDetectionStatement.{u, v} := by
    intro k _ _ _ _ G hG T i hi
    let := hG.isAffineHom
    let := hi.isSplitSubtorus.mono
    let : TopologicalSpace (RationalPoint k G.X) := pointTopology
    intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
    let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
    exact ExactnessDetection.supportCategoryExactnessDetection_of_zeroDetection
      (fun J =>
        standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
          i ν hStandard hG hi hν J)
      (hzero k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM)
  -- Step 5: corrected Theorem 3.6 with explicit structural premises.
  have hrat : RationalCorrectedTheorem36Statement.{u, v} :=
    rationalCorrectedTheorem36_of_inputs.{u, v}
      { bruhat := Langlands.GroupScheme.rationalBruhat.{u}
        gradedVanishing := hvan
        gradedTransition := rationalCorrectedGradedTransitionStatement.{u, v}
        inductionJacquet := hind
        exactnessDetection := hdet }
  -- Step 6: specialization to the canonical structural data.
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  intro ν hν _ I
  exact hrat k G hG T i hi ν hν
    standardCocharacter
    standardParabolicOrder
    standardParabolicEndpoints
    standardLeviIntersection
    (relativeRootSystem k G hG T i hi)
    (canonicalPointNormalizerComparison hG i hi)
    (canonicalPointCentralizerComparison hG i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (canonicalStandardLevi_isClosed i ν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν) I

end Langlands.Aubert.General.RationalPointFamily
