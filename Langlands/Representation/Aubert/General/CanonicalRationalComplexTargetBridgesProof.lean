import Langlands.Representation.Aubert.General.CanonicalRationalComplexTargets

/-! # Proof that the existing Family 3/4 rational-point targets imply their canonical forms -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.Group.RelativeWeylIndexing

/-- The existing `RationalCorrectedTheorem36Statement` implies its canonical form. -/
theorem canonicalRationalCorrectedTheorem36_of_rational
    (h : RationalCorrectedTheorem36Statement.{u, v}) :
    CanonicalRationalCorrectedTheorem36Statement.{u, v} := by
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
      i ν standardCocharacter hG hi hν) I

/-- The existing `RationalFixedLeviComparisonStatement` implies its canonical form. -/
theorem canonicalRationalFixedLeviComparison_of_rational
    (h : RationalFixedLeviComparisonStatement.{u, v}) :
    CanonicalRationalFixedLeviComparisonStatement.{u, v} := by
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
  intro ν hν _
  exact h k G hG T i hi ν hν
    standardCocharacter
    standardParabolicOrder
    standardLeviIntersection
    (relativeRootSystem k G hG T i hi)
    (canonicalPointNormalizerComparison hG i hi)
    (canonicalPointCentralizerComparison hG i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (canonicalStandardLevi_isClosed i ν)
    (canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups hG i ν hi hν)

/-- The existing `RationalAssociatedLeviComparisonStatement` implies its canonical form. -/
theorem canonicalRationalAssociatedLeviComparison_of_rational
    (h : RationalAssociatedLeviComparisonStatement.{u, v}) :
    CanonicalRationalAssociatedLeviComparisonStatement.{u, v} := by
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

/-- The existing `RationalSharpFiniteLengthStatement` implies its canonical form. -/
theorem canonicalRationalSharpFiniteLength_of_rational
    (h : RationalSharpFiniteLengthStatement.{u, v}) :
    CanonicalRationalSharpFiniteLengthStatement.{u, v} := by
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
  intro ν hν _
  exact h k G hG T i hi ν hν
    standardCocharacter
    standardParabolicOrder
    (relativeRootSystem k G hG T i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)

/-- The existing `RationalSharpClassFormulaStatement` implies its canonical form. -/
theorem canonicalRationalSharpClassFormula_of_rational
    (h : RationalSharpClassFormulaStatement.{u, v}) :
    CanonicalRationalSharpClassFormulaStatement.{u, v} := by
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
  intro ν hν _
  exact h k G hG T i hi ν hν
    standardCocharacter
    standardParabolicOrder
    standardLeviIntersection
    (relativeRootSystem k G hG T i hi)
    (canonicalPointNormalizerComparison hG i hi)
    (canonicalPointCentralizerComparison hG i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (canonicalStandardLevi_isClosed i ν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)

/-- The existing `RationalSharpSupportRetentionStatement` implies its canonical form. -/
theorem canonicalRationalSharpSupportRetention_of_rational
    (h : RationalSharpSupportRetentionStatement.{u, v}) :
    CanonicalRationalSharpSupportRetentionStatement.{u, v} := by
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
  intro ν hν _
  exact h k G hG T i hi ν hν
    standardCocharacter
    standardParabolicOrder
    standardLeviIntersection
    (relativeRootSystem k G hG T i hi)
    (canonicalPointNormalizerComparison hG i hi)
    (canonicalPointCentralizerComparison hG i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (canonicalStandardLevi_isClosed i ν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)

/-- The existing `RationalSharpIrreducibleStatement` implies its canonical form. -/
theorem canonicalRationalSharpIrreducible_of_rational
    (h : RationalSharpIrreducibleStatement.{u, v}) :
    CanonicalRationalSharpIrreducibleStatement.{u, v} := by
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
  intro ν hν _
  exact h k G hG T i hi ν hν
    standardCocharacter
    standardParabolicOrder
    standardLeviIntersection
    (relativeRootSystem k G hG T i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (canonicalStandardLevi_isClosed i ν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)

/-- The existing `RationalSharpCuspidalSeriesStatement` implies its canonical form. -/
theorem canonicalRationalSharpCuspidalSeries_of_rational
    (h : RationalSharpCuspidalSeriesStatement.{u, v}) :
    CanonicalRationalSharpCuspidalSeriesStatement.{u, v} := by
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
  intro ν hν _
  exact h k G hG T i hi ν hν
    standardCocharacter
    standardParabolicOrder
    standardLeviIntersection
    (relativeRootSystem k G hG T i hi)
    (canonicalPointNormalizerComparison hG i hi)
    (canonicalPointCentralizerComparison hG i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (canonicalStandardLevi_isClosed i ν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)

/-- The existing `RationalSharpInvolutionStatement` implies its canonical form. -/
theorem canonicalRationalSharpInvolution_of_rational
    (h : RationalSharpInvolutionStatement.{u, v}) :
    CanonicalRationalSharpInvolutionStatement.{u, v} := by
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
  intro ν hν _
  exact h k G hG T i hi ν hν
    standardCocharacter
    standardParabolicOrder
    standardLeviIntersection
    (relativeRootSystem k G hG T i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (canonicalStandardLevi_isClosed i ν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)

/-- Each existing Family 3/4 rational-point target implies its canonical form. -/
theorem canonicalRationalComplexTargetBridges :
    CanonicalRationalComplexTargetBridgesStatement.{u, v} :=
  ⟨canonicalRationalCorrectedTheorem36_of_rational,
    canonicalRationalFixedLeviComparison_of_rational,
    canonicalRationalAssociatedLeviComparison_of_rational,
    canonicalRationalSharpFiniteLength_of_rational,
    canonicalRationalSharpClassFormula_of_rational,
    canonicalRationalSharpSupportRetention_of_rational,
    canonicalRationalSharpIrreducible_of_rational,
    canonicalRationalSharpCuspidalSeries_of_rational,
    canonicalRationalSharpInvolution_of_rational⟩

end Langlands.Aubert.General.RationalPointFamily
