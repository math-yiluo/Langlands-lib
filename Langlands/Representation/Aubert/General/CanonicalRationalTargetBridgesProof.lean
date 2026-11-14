import Langlands.Representation.Aubert.General.CanonicalRationalTargetBridgesStatement

/-! # Proof that existing rational-point Aubert targets imply their canonical forms -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

theorem canonicalRationalInvolutivity_of_rational
    (h : RationalInvolutivityStatement.{u, v}) :
    CanonicalRationalInvolutivityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  let := hi.isSplitSubtorus.mono
  intro ν hν hiFl hrFl
  exact h k G hG T i hi ν hν standardCocharacter (relativeRootSystem k G hG T i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)

theorem canonicalRationalContragredientCommutation_of_rational
    (h : RationalContragredientCommutationStatement.{u, v}) :
    CanonicalRationalContragredientCommutationStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  let := hi.isSplitSubtorus.mono
  intro ν hν hiFl hrFl hc
  exact h k G hG T i hi ν hν standardCocharacter (relativeRootSystem k G hG T i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl) hc

theorem canonicalRationalCuspidalEigenvalue_of_rational
    (h : RationalCuspidalEigenvalueStatement.{u, v}) :
    CanonicalRationalCuspidalEigenvalueStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  let := hi.isSplitSubtorus.mono
  intro ν hν hiFl hrFl
  exact h k G hG T i hi ν hν standardCocharacter (relativeRootSystem k G hG T i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)

theorem canonicalRationalInductionCompatibility_of_rational
    (h : RationalInductionCompatibilityStatement.{u, v}) :
    CanonicalRationalInductionCompatibilityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  let := hi.isSplitSubtorus.mono
  intro ν hν hiFl hrFl
  exact h k G hG T i hi ν hν standardCocharacter (relativeRootSystem k G hG T i hi)
    standardLeviIntersection
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)
    (canonicalStandardLevi_isClosed i ν)
    (canonicalStandardLeviProjection_continuous hG i ν hi hν)
    (canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups hG i ν hi hν)
    (canonicalStandardLeviInduction_preservesFiniteLength hG i ν hi hν hiFl)
    (canonicalStandardLeviJacquet_preservesFiniteLength hG i ν hi hν hiFl hrFl)

theorem canonicalRationalJacquetCompatibility_of_rational
    (h : RationalJacquetCompatibilityStatement.{u, v}) :
    CanonicalRationalJacquetCompatibilityStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  let := hi.isSplitSubtorus.mono
  intro ν hν hiFl hrFl _ _
  let _ : Fintype (SimpleRoot i ν) := simpleRelativeRootFintype i
    (relativeRootSystem k G hG T i hi) hi.isSplitSubtorus.1 ν
  exact h k G hG T i hi ν hν standardCocharacter (relativeRootSystem k G hG T i hi)
    standardLeviIntersection
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)
    (canonicalStandardLevi_isClosed i ν)
    (canonicalStandardLeviProjection_continuous hG i ν hi hν)
    (canonicalStandardLeviUnipotent_isLimitOfCompactSubgroups hG i ν hi hν)
    (canonicalStandardLeviInduction_preservesFiniteLength hG i ν hi hν hiFl)
    (canonicalStandardLeviJacquet_preservesFiniteLength hG i ν hi hν hiFl hrFl)
    standardLeviConjugation
    (canonicalPointNormalizerComparison hG i hi)
    (canonicalPointCentralizerComparison hG i hi)
    (canonicalCoxeterMatrix hG i hi ν hν) (canonicalCoxeterSystem hG i hi ν hν)
    (canonicalRootLengthComparison hG i hi ν hν)
    (canonicalPositiveSimpleReflectionComparison hG i hi ν hν)
    (canonicalMinimalityLengthCriterion hG i hi ν hν)
    (canonicalAssociatedSubsetLaws hG i hi ν hν)

theorem canonicalRationalCorollary110a_of_rational
    (h : RationalCorollary110aStatement.{u, v}) :
    CanonicalRationalCorollary110aStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  let := hi.isSplitSubtorus.mono
  intro ν hν hiFl hrFl
  exact h k G hG T i hi ν hν standardCocharacter standardLeviIntersection
    (relativeRootSystem k G hG T i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (canonicalStandardLevi_isClosed i ν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)

theorem canonicalRationalCorollary110b_of_rational
    (h : RationalCorollary110bStatement.{u, v}) :
    CanonicalRationalCorollary110bStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  let := hi.isSplitSubtorus.mono
  intro ν hν hiFl hrFl
  exact h k G hG T i hi ν hν standardCocharacter standardLeviIntersection
    (relativeRootSystem k G hG T i hi)
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (canonicalStandardLevi_isClosed i ν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)

theorem canonicalRationalInducedK0WeylConjugacy_of_rational
    (h : RationalInducedK0WeylConjugacyStatement.{u, v}) :
    CanonicalRationalInducedK0WeylConjugacyStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let : Smooth G.X.hom := hG.smooth
  let : T2Space k := BruhatTits.localField_t2Space k
  let : LocallyCompactSpace (RationalPoint k G.X) := rationalPoint_locallyCompactSpace k G
  let : NonarchimedeanGroup (RationalPoint k G.X) :=
    Plancherel.rationalPoints_nonarchimedeanGroup G
  let : T2Space (RationalPoint k G.X) := rationalPoint_t2Space k G
  intro ν hν hiFl hrFl
  exact h k G hG T i hi ν hν standardCocharacter
    (canonicalStandardUnipotent_isClosed hG i ν hi hν)
    (standardParabolic_isClosed_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (continuous_standard_projection i ν standardCocharacter hG hi hν)
    (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν standardCocharacter hG hi hν)
    (standardInduction_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hiFl)
    (standardJacquet_preservesFiniteLength_of_dynamic i ν standardCocharacter hG hi hν
      (canonicalStandardUnipotent_isClosed hG i ν hi hν) hrFl)

theorem canonicalRationalTargetBridges :
    CanonicalRationalTargetBridgesStatement.{u, v} :=
  ⟨canonicalRationalContragredientCommutation_of_rational,
    canonicalRationalInductionCompatibility_of_rational,
    canonicalRationalJacquetCompatibility_of_rational,
    canonicalRationalInvolutivity_of_rational,
    canonicalRationalCuspidalEigenvalue_of_rational,
    canonicalRationalCorollary110a_of_rational,
    canonicalRationalCorollary110b_of_rational,
    canonicalRationalInducedK0WeylConjugacy_of_rational⟩

end Langlands.Aubert.General.RationalPointFamily
