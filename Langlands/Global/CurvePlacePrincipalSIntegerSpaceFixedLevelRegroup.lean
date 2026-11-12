import Langlands.Global.CurvePlacePrincipalSIntegerSpaceFixedLevelWeil
import Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelRegroup

/-! # Original upper-place regrouping of curve-place space Weil stages -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain IntermediateField AlgebraicCurve
open _root_.AlgebraicGeometry
open scoped TensorProduct AlgebraicCurve.CurveModel IntermediateField.algebraAdjoinAdjoin
  Langlands.Global Langlands.Global.CurvePlacePrincipalSIntegers
  Langlands.Global.CurvePlacePrincipalSIntegerFixedLevelWeil
  Langlands.Global.FixedModelLocalProduct
  Langlands.Global.AdelicSpaceStageCoordinates

namespace Langlands.Global.CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open CurvePlacePrincipalSIntegerFixedLevelWeil
open CurvePlacePrincipalSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)
open CurvePlacePrincipalSIntegerSpaceFixedLevelWeil (upperFieldAlgHom)

set_option backward.isDefEq.respectTransparency false

variable (k K L : Type u) [Field k] [Finite k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [Algebra (RatFunc k) K] [IsScalarTower k (RatFunc k) K] [FunctionField k K]
  [FiniteDimensional K L] (s : K) [FiniteDimensional k⟮s⟯ K]
  (t : CurveModel.chartRing k ({s} : Set K)) [Fact (t ≠ 0)]
  (T : AdelicLevelIndexAbove (curvePlacePrincipalExceptional k K s (t : K)))

/-- The original upper enlarged support is the full preimage of the lower one. -/
abbrev upperLevel := CurvePlacePrincipalSIntegerFixedLevelRegroup.upperLevel k K L s t T

/-- The original reindexing of upper local places. -/
abbrev indexEquiv := CurvePlacePrincipalSIntegerFixedLevelRegroup.indexEquiv k K L s t T

variable (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients k K L s t))))

set_option maxHeartbeats 800000 in
/-- Regrouping keeps the original coefficient ring, actual local field
or integer ring, and original field-valued point topology. -/
def factorPointHomeomorph (z : Σ i, Above k K L s t T i) :
    letI := fieldValuedPointTopology (upperCoefficients k K L s t) X
      (upperFieldAlgHom k K L s t T z.1 z.2)
    letI := fieldValuedPointTopology (upperCoefficients k K L s t) X
      ((curvePlaceLevelFieldAlgHom k L (upperLevel k K L s t T).val
        (indexEquiv k K L s t T z)).restrictScalars _)
    RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2) ≃ₜ
      RingPoints (upperCoefficients k K L s t) X
        (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val (indexEquiv k K L s t T z)) := by
  letI := fieldValuedPointTopology (upperCoefficients k K L s t) X
    (upperFieldAlgHom k K L s t T z.1 z.2)
  letI := fieldValuedPointTopology (upperCoefficients k K L s t) X
    ((curvePlaceLevelFieldAlgHom k L (upperLevel k K L s t T).val
      (indexEquiv k K L s t T z)).restrictScalars _)
  rcases z with ⟨i, q⟩
  cases i <;> exact Homeomorph.refl _

/-- The upper local factors, regrouped by actual upper places, carry
precisely the upper stage coordinate product topology. -/
def productPointHomeomorph :
    letI : ∀ z : Σ i, Above k K L s t T i, TopologicalSpace
        (RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) :=
      fun z => fieldValuedPointTopology (upperCoefficients k K L s t) X
        (upperFieldAlgHom k K L s t T z.1 z.2)
    letI : ∀ j : CurvePlaceLevelFactorIndex k L (upperLevel k K L s t T).val, TopologicalSpace
        (RingPoints (upperCoefficients k K L s t) X (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j)) :=
      fun j => fieldValuedPointTopology (upperCoefficients k K L s t) X
        ((curvePlaceLevelFieldAlgHom k L (upperLevel k K L s t T).val j).restrictScalars _)
    (∀ z : Σ i, Above k K L s t T i,
      RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) ≃ₜ
    (∀ j : CurvePlaceLevelFactorIndex k L (upperLevel k K L s t T).val,
      RingPoints (upperCoefficients k K L s t) X (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j)) := by
  let (z : Σ i, Above k K L s t T i) : TopologicalSpace
      (RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X (upperFieldAlgHom k K L s t T z.1 z.2)
  let (j : CurvePlaceLevelFactorIndex k L (upperLevel k K L s t T).val) : TopologicalSpace
      (RingPoints (upperCoefficients k K L s t) X (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X
      ((curvePlaceLevelFieldAlgHom k L (upperLevel k K L s t T).val j).restrictScalars _)
  exact (Homeomorph.piCongrRight (factorPointHomeomorph k K L s t T X)).trans
    (Homeomorph.piCongrLeft (Y := fun j => RingPoints (upperCoefficients k K L s t) X
      (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j)) (indexEquiv k K L s t T))

omit [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
@[simp]
theorem productPointHomeomorph_apply
    (x : ∀ z : Σ i, Above k K L s t T i,
      RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2))
    (z : Σ i, Above k K L s t T i) :
    productPointHomeomorph k K L s t T X x (indexEquiv k K L s t T z) =
      factorPointHomeomorph k K L s t T X z (x z) := by
  let (z : Σ i, Above k K L s t T i) : TopologicalSpace
      (RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X (upperFieldAlgHom k K L s t T z.1 z.2)
  let (j : CurvePlaceLevelFactorIndex k L (upperLevel k K L s t T).val) : TopologicalSpace
      (RingPoints (upperCoefficients k K L s t) X (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X
      ((curvePlaceLevelFieldAlgHom k L (upperLevel k K L s t T).val j).restrictScalars _)
  change (Homeomorph.piCongrLeft (Y := fun j => RingPoints (upperCoefficients k K L s t) X
    (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j)) (indexEquiv k K L s t T))
      ((Homeomorph.piCongrRight (factorPointHomeomorph k K L s t T X)) x)
      (indexEquiv k K L s t T z) = _
  exact Homeomorph.piCongrLeft_apply_apply (Y := fun j => RingPoints (upperCoefficients k K L s t) X
    (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j))
    (indexEquiv k K L s t T) ((Homeomorph.piCongrRight (factorPointHomeomorph k K L s t T X)) x) z

variable
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients k K s t) (upperCoefficients k K L s t)).obj X.toSheaf))
  (hsep : IsSeparated X) (hft : FiniteTypeOverRing (upperCoefficients k K L s t) X)
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients k K s t)
    (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h))

variable [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  (hS : (curvePlacePrincipalExceptional k K s (t : K)).Nonempty)

include hS in
omit [Algebra (RatFunc k) L] [IsScalarTower k (RatFunc k) L] [FunctionField k L]
  [FiniteDimensional k⟮s⟯ K] [Fact (t ≠ 0)] in
/-- A nonempty lower support has a nonempty full upper preimage. -/
theorem upperSupport_nonempty :
    (curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))).Nonempty := by
  obtain ⟨p, hp⟩ := hS
  obtain ⟨q, hq⟩ := curvePlaceRestriction_surjective (L := L) p
  refine ⟨q, (mem_curvePlaceExceptionalPreimage _ q).mpr ?_⟩
  simpa only [hq] using hp

/-- Actual enlarged stages of the two fixed original models are
homeomorphic through the original tensor comparison and upper-place regrouping. -/
def adelicLevelPointHomeomorph :
    letI := curvePlaceSpaceStageTopology k K (curvePlacePrincipalExceptional k K s (t : K))
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h) T
    letI := curvePlaceSpaceStageTopology k L ((curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) X
      (upperLevel k K L s t T)
    RingPoints (lowerCoefficients k K s t)
        (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
        (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T) ≃ₜ
      RingPoints (upperCoefficients k K L s t) X
        (curvePlaceAdeleLevelOver k L ((curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K))))
          (upperLevel k K L s t T)) := by
  let W := ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h
  let : TopologicalSpace (RingPoints (lowerCoefficients k K s t) W (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :=
    curvePlaceSpaceStageTopology k K (curvePlacePrincipalExceptional k K s (t : K)) W T
  let : TopologicalSpace (RingPoints (upperCoefficients k K L s t) X
      (curvePlaceAdeleLevelOver k L ((curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (upperLevel k K L s t T))) :=
    curvePlaceSpaceStageTopology k L ((curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) X (upperLevel k K L s t T)
  let (z : Σ i, Above k K L s t T i) : TopologicalSpace
      (RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X (upperFieldAlgHom k K L s t T z.1 z.2)
  let (j : CurvePlaceLevelFactorIndex k L (upperLevel k K L s t T).val) : TopologicalSpace
      (RingPoints (upperCoefficients k K L s t) X (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X
      ((curvePlaceLevelFieldAlgHom k L (upperLevel k K L s t T).val j).restrictScalars _)
  exact (CurvePlacePrincipalSIntegerSpaceFixedLevelWeil.levelPointHomeomorph k K L s t T X h
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hsep) hft hWsep hWft hS).trans
    ((productPointHomeomorph k K L s t T X).trans
      (AdelicSpaceStageCoordinates.curveStageHomeomorph k L
        ((curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (upperLevel k K L s t T) X hsep hft (upperSupport_nonempty k K L s t hS)).symm)

/-- The comparison of actual stages has exactly the previously constructed
original local components after upper coordinate evaluation. -/
theorem adelicLevelPointHomeomorph_coordinates
    (x : RingPoints (lowerCoefficients k K s t)
      (ringWeilRestrictionSpace (lowerCoefficients k K s t) (upperCoefficients k K L s t) X h)
      (curvePlaceAdeleLevelOver k K (curvePlacePrincipalExceptional k K s (t : K)) T)) :
    AdelicSpaceStageCoordinates.curveStageHomeomorph k L
        ((curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (upperLevel k K L s t T) X hsep hft (upperSupport_nonempty k K L s t hS)
        (adelicLevelPointHomeomorph k K L s t T X h hsep hft hWsep hWft hS x) =
      productPointHomeomorph k K L s t T X
        (CurvePlacePrincipalSIntegerSpaceFixedLevelWeil.levelPointHomeomorph k K L s t T X h
          (SpaceProductPoints.isQuasiSeparated_of_isSeparated hsep) hft hWsep hWft hS x) := by
  let (z : Σ i, Above k K L s t T i) : TopologicalSpace
      (RingPoints (upperCoefficients k K L s t) X (upperFactor k K L s t T z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X (upperFieldAlgHom k K L s t T z.1 z.2)
  let (j : CurvePlaceLevelFactorIndex k L (upperLevel k K L s t T).val) : TopologicalSpace
      (RingPoints (upperCoefficients k K L s t) X (CurvePlaceLevelFactor k L (upperLevel k K L s t T).val j)) :=
    fieldValuedPointTopology (upperCoefficients k K L s t) X
      ((curvePlaceLevelFieldAlgHom k L (upperLevel k K L s t T).val j).restrictScalars _)
  let : TopologicalSpace (RingPoints (upperCoefficients k K L s t) X
      (curvePlaceAdeleLevelOver k L ((curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (upperLevel k K L s t T))) :=
    curvePlaceSpaceStageTopology k L ((curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) X (upperLevel k K L s t T)
  exact (AdelicSpaceStageCoordinates.curveStageHomeomorph k L
    ((curvePlaceExceptionalPreimage (L := L) (curvePlacePrincipalExceptional k K s (t : K)))) (upperLevel k K L s t T) X hsep hft (upperSupport_nonempty k K L s t hS)).apply_symm_apply _

end Langlands.Global.CurvePlacePrincipalSIntegerSpaceFixedLevelRegroup
