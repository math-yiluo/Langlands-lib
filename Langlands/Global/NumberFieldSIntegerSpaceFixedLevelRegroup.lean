import Langlands.Global.NumberFieldSIntegerSpaceFixedLevelWeil
import Langlands.Global.NumberFieldSIntegerFixedLevelRegroup

/-! # Original upper-place regrouping of number-field space Weil stages -/

noncomputable section

universe u

open CategoryTheory Topology IsDedekindDomain
open _root_.AlgebraicGeometry
open scoped NumberField TensorProduct NumberField.LiesOver
  Langlands.Global Langlands.Global.NumberFieldSIntegers
  Langlands.Global.NumberFieldSIntegerLevelWeil
  Langlands.Global.NumberFieldSIntegerFixedLevelWeil
  Langlands.Global.FixedModelLocalProduct
  Langlands.Global.AdelicSpaceStageCoordinates

namespace Langlands.Global.NumberFieldSIntegerSpaceFixedLevelRegroup

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace
open NumberFieldSIntegerLevelWeil
open NumberFieldSIntegerSpaceWeilTopology (lowerCoefficients upperCoefficients)
open NumberFieldSIntegerSpaceFixedLevelWeil (upperFieldAlgHom)

set_option backward.isDefEq.respectTransparency false

attribute [local instance] NumberFieldSIntegerSpaceFixedLevelWeil.upperFieldField
  NumberFieldSIntegerSpaceFixedLevelWeil.upperFieldTopology
  NumberFieldSIntegerSpaceFixedLevelWeil.upperFieldCoefficientAlgebra

variable (K L : Type u) [Field K] [Field L] [NumberField K] [NumberField L]
  [Algebra K L] (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)

/-- The original upper enlarged support is the full preimage of the lower one. -/
abbrev upperLevel := NumberFieldSIntegerFixedLevelRegroup.upperLevel K L S T

/-- The original reindexing of upper local places. -/
abbrev indexEquiv := NumberFieldSIntegerFixedLevelRegroup.indexEquiv K L S T

variable (X : AlgebraicSpace (Spec (CommRingCat.of (upperCoefficients K L S))))

set_option maxHeartbeats 800000 in
/-- Regrouping keeps the original coefficient ring, actual local field
or integer ring, and original field-valued point topology. -/
def factorPointHomeomorph (z : Σ i, Above K L T.val i) :
    letI := fieldValuedPointTopology (upperCoefficients K L S) X
      (upperFieldAlgHom K L S T z.1 z.2)
    letI := fieldValuedPointTopology (upperCoefficients K L S) X
      ((numberFieldLevelFieldAlgHom L (upperLevel K L S T).val
        (indexEquiv K L S T z)).restrictScalars _)
    RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2) ≃ₜ
      RingPoints (upperCoefficients K L S) X
        (NumberFieldLevelFactor L (upperLevel K L S T).val (indexEquiv K L S T z)) := by
  letI := fieldValuedPointTopology (upperCoefficients K L S) X
    (upperFieldAlgHom K L S T z.1 z.2)
  letI := fieldValuedPointTopology (upperCoefficients K L S) X
    ((numberFieldLevelFieldAlgHom L (upperLevel K L S T).val
      (indexEquiv K L S T z)).restrictScalars _)
  rcases z with ⟨i, q⟩
  cases i with
  | inl p => exact Homeomorph.refl _
  | inr z => cases z <;> exact Homeomorph.refl _

/-- The upper local factors, regrouped by actual upper places, carry
precisely the upper stage coordinate product topology. -/
def productPointHomeomorph :
    letI : ∀ z : Σ i, Above K L T.val i, TopologicalSpace
        (RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) :=
      fun z => fieldValuedPointTopology (upperCoefficients K L S) X
        (upperFieldAlgHom K L S T z.1 z.2)
    letI : ∀ j : NumberFieldLevelFactorIndex L (upperLevel K L S T).val, TopologicalSpace
        (RingPoints (upperCoefficients K L S) X (NumberFieldLevelFactor L (upperLevel K L S T).val j)) :=
      fun j => fieldValuedPointTopology (upperCoefficients K L S) X
        ((numberFieldLevelFieldAlgHom L (upperLevel K L S T).val j).restrictScalars _)
    (∀ z : Σ i, Above K L T.val i,
      RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) ≃ₜ
    (∀ j : NumberFieldLevelFactorIndex L (upperLevel K L S T).val,
      RingPoints (upperCoefficients K L S) X (NumberFieldLevelFactor L (upperLevel K L S T).val j)) := by
  let (z : Σ i, Above K L T.val i) : TopologicalSpace
      (RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X (upperFieldAlgHom K L S T z.1 z.2)
  let (j : NumberFieldLevelFactorIndex L (upperLevel K L S T).val) : TopologicalSpace
      (RingPoints (upperCoefficients K L S) X (NumberFieldLevelFactor L (upperLevel K L S T).val j)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X
      ((numberFieldLevelFieldAlgHom L (upperLevel K L S T).val j).restrictScalars _)
  exact (Homeomorph.piCongrRight (factorPointHomeomorph K L S T X)).trans
    (Homeomorph.piCongrLeft (Y := fun j => RingPoints (upperCoefficients K L S) X
      (NumberFieldLevelFactor L (upperLevel K L S T).val j)) (indexEquiv K L S T))

@[simp]
theorem productPointHomeomorph_apply
    (x : ∀ z : Σ i, Above K L T.val i,
      RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2))
    (z : Σ i, Above K L T.val i) :
    productPointHomeomorph K L S T X x (indexEquiv K L S T z) =
      factorPointHomeomorph K L S T X z (x z) := by
  let (z : Σ i, Above K L T.val i) : TopologicalSpace
      (RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X (upperFieldAlgHom K L S T z.1 z.2)
  let (j : NumberFieldLevelFactorIndex L (upperLevel K L S T).val) : TopologicalSpace
      (RingPoints (upperCoefficients K L S) X (NumberFieldLevelFactor L (upperLevel K L S T).val j)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X
      ((numberFieldLevelFieldAlgHom L (upperLevel K L S T).val j).restrictScalars _)
  change (Homeomorph.piCongrLeft (Y := fun j => RingPoints (upperCoefficients K L S) X
    (NumberFieldLevelFactor L (upperLevel K L S T).val j)) (indexEquiv K L S T))
      ((Homeomorph.piCongrRight (factorPointHomeomorph K L S T X)) x)
      (indexEquiv K L S T z) = _
  exact Homeomorph.piCongrLeft_apply_apply (Y := fun j => RingPoints (upperCoefficients K L S) X
    (NumberFieldLevelFactor L (upperLevel K L S T).val j))
    (indexEquiv K L S T) ((Homeomorph.piCongrRight (factorPointHomeomorph K L S T X)) x) z

variable
  (h : IsAlgebraicSpace _
    ((ringWeilRestriction (lowerCoefficients K S) (upperCoefficients K L S)).obj X.toSheaf))
  (hsep : IsSeparated X) (hft : FiniteTypeOverRing (upperCoefficients K L S) X)
  (hWsep : IsSeparated
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))
  (hWft : FiniteTypeOverRing (lowerCoefficients K S)
    (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h))

/-- Actual enlarged stages of the two fixed original models are
homeomorphic through the original tensor comparison and upper-place regrouping. -/
def adelicLevelPointHomeomorph :
    letI := numberFieldSpaceStageTopology K S
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h) T
    letI := numberFieldSpaceStageTopology L (numberFieldExceptionalPreimage (L := L) S) X
      (upperLevel K L S T)
    RingPoints (lowerCoefficients K S)
        (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
        (numberFieldAdeleLevelOver K S T) ≃ₜ
      RingPoints (upperCoefficients K L S) X
        (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S)
          (upperLevel K L S T)) := by
  let W := ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h
  let : TopologicalSpace (RingPoints (lowerCoefficients K S) W (numberFieldAdeleLevelOver K S T)) :=
    numberFieldSpaceStageTopology K S W T
  let : TopologicalSpace (RingPoints (upperCoefficients K L S) X
      (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T))) :=
    numberFieldSpaceStageTopology L (numberFieldExceptionalPreimage (L := L) S) X (upperLevel K L S T)
  let (z : Σ i, Above K L T.val i) : TopologicalSpace
      (RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X (upperFieldAlgHom K L S T z.1 z.2)
  let (j : NumberFieldLevelFactorIndex L (upperLevel K L S T).val) : TopologicalSpace
      (RingPoints (upperCoefficients K L S) X (NumberFieldLevelFactor L (upperLevel K L S T).val j)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X
      ((numberFieldLevelFieldAlgHom L (upperLevel K L S T).val j).restrictScalars _)
  exact (NumberFieldSIntegerSpaceFixedLevelWeil.levelPointHomeomorph K L S T X h
    (SpaceProductPoints.isQuasiSeparated_of_isSeparated hsep) hft hWsep hWft).trans
    ((productPointHomeomorph K L S T X).trans
      (AdelicSpaceStageCoordinates.numberFieldStageHomeomorph L
        (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T) X hsep hft).symm)

/-- The comparison of actual stages has exactly the previously constructed
original local components after upper coordinate evaluation. -/
theorem adelicLevelPointHomeomorph_coordinates
    (x : RingPoints (lowerCoefficients K S)
      (ringWeilRestrictionSpace (lowerCoefficients K S) (upperCoefficients K L S) X h)
      (numberFieldAdeleLevelOver K S T)) :
    AdelicSpaceStageCoordinates.numberFieldStageHomeomorph L
        (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T) X hsep hft
        (adelicLevelPointHomeomorph K L S T X h hsep hft hWsep hWft x) =
      productPointHomeomorph K L S T X
        (NumberFieldSIntegerSpaceFixedLevelWeil.levelPointHomeomorph K L S T X h
          (SpaceProductPoints.isQuasiSeparated_of_isSeparated hsep) hft hWsep hWft x) := by
  let (z : Σ i, Above K L T.val i) : TopologicalSpace
      (RingPoints (upperCoefficients K L S) X (upperFactor K L T.val z.1 z.2)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X (upperFieldAlgHom K L S T z.1 z.2)
  let (j : NumberFieldLevelFactorIndex L (upperLevel K L S T).val) : TopologicalSpace
      (RingPoints (upperCoefficients K L S) X (NumberFieldLevelFactor L (upperLevel K L S T).val j)) :=
    fieldValuedPointTopology (upperCoefficients K L S) X
      ((numberFieldLevelFieldAlgHom L (upperLevel K L S T).val j).restrictScalars _)
  let : TopologicalSpace (RingPoints (upperCoefficients K L S) X
      (numberFieldAdeleLevelOver L (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T))) :=
    numberFieldSpaceStageTopology L (numberFieldExceptionalPreimage (L := L) S) X (upperLevel K L S T)
  exact (AdelicSpaceStageCoordinates.numberFieldStageHomeomorph L
    (numberFieldExceptionalPreimage (L := L) S) (upperLevel K L S T) X hsep hft).apply_symm_apply _

end Langlands.Global.NumberFieldSIntegerSpaceFixedLevelRegroup
