import Langlands.Representation.Aubert.General.CanonicalRationalComplexReductionStatements
import Langlands.Representation.Aubert.General.RationalAssociatedLeviReduction
import Langlands.Representation.Aubert.General.RationalCorrectedSurvivingSupportProof
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitRadicalProof
import Langlands.Representation.Aubert.General.RationalCorrectedOrbitModulusProof
import Langlands.Representation.Aubert.General.RationalCorrectedGradedTransitionProof
import Langlands.GroupScheme.Rational.RationalBruhatProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-! # Proof of the reduction of the canonical associated-Levi comparison to graded vanishing -/

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- Corrected graded vanishing implies the associated-Levi Jacquet comparison
(display (**) of the erratum, p.4690) for the canonical actual families. -/
theorem canonicalRationalAssociatedLeviComparisonReduction :
    CanonicalRationalAssociatedLeviComparisonReductionStatement.{u, v} := by
  intro hvan
  -- The rational target, with its structural premises still explicit.
  have h : RationalAssociatedLeviComparisonStatement.{u, v} :=
    rationalAssociatedLeviComparisonStatement_of_published.{u, v}
      Langlands.GroupScheme.rationalBruhat.{u}
      Langlands.BruhatTits.dynamicParabolicQuotientCompact.{u}
      rationalCorrectedSurvivingSupport.{u}
      rationalCorrectedOrbitRadicalIntersectionStatement.{u}
      rationalCorrectedOrbitSquaredModulus.{u}
      hvan
      rationalCorrectedGradedTransitionStatement.{u, v}
  -- Instantiate it at the published canonical structural data.
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
  intro ν hν _ _
  let _ : Fintype (SimpleRoot i ν) :=
    simpleRelativeRootFintype i (relativeRootSystem k G hG T i hi) hi.isSplitSubtorus.1 ν
  exact h k G hG T i hi ν hν
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
      i ν standardCocharacter hG hi hν)
    (canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups hG i ν hi hν)
    (canonicalCoxeterMatrix hG i hi ν hν) (canonicalCoxeterSystem hG i hi ν hν)
    (canonicalRootLengthComparison hG i hi ν hν)
    (canonicalPositiveSimpleReflectionComparison hG i hi ν hν)
    (canonicalLeviWeylIdentification hG i hi ν hν)
    (canonicalMinimalityLengthCriterion hG i hi ν hν)
    (canonicalAssociatedSubsetLaws hG i hi ν hν)
    (canonicalAssociatedLeviConjugation hG i hi ν hν)

end Langlands.Aubert.General.RationalPointFamily
