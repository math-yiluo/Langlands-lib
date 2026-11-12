import Langlands.Global.AdelicSpacePointTopology
import Langlands.Global.AdelicFixedModelLocalProductTopology
import Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointOpenMap

/-! # Original fixed-base coordinates of algebraic-space adelic stages -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

section FieldBaseChange

variable (C C' : Type u) [CommRing C] [CommRing C'] [Algebra C C']
  (X : AlgebraicSpace (Spec (CommRingCat.of C)))
  {A L : Type u} [CommRing A] [Algebra C' A] [Algebra C A] [IsScalarTower C C' A]
  [Field L] [Algebra C' L] [Algebra C L] [IsScalarTower C C' L]
  [TopologicalSpace L]

/-- Original field-valued topologies commute with base change of the
coefficient ring along the canonical point equivalence. -/
def fieldValuedBaseChangeHomeomorph (ψ : A →ₐ[C'] L) :
    letI := fieldValuedPointTopology C' (baseChange (Spec.algebraMap C C') X) ψ
    letI := fieldValuedPointTopology C X (ψ.restrictScalars C)
    RingPoints C' (baseChange (Spec.algebraMap C C') X) A ≃ₜ RingPoints C X A := by
  let : TopologicalSpace (RingPoints C' (baseChange (Spec.algebraMap C C') X) A) :=
    fieldValuedPointTopology C' (baseChange (Spec.algebraMap C C') X) ψ
  let : TopologicalSpace (RingPoints C X A) :=
    fieldValuedPointTopology C X (ψ.restrictScalars C)
  exact (baseChangeRingPointsEquiv C C' A X).toHomeomorphOfIsInducing
    ⟨CoordinatePointTopologyFacts.fieldValuedPointTopology_baseChange X ψ⟩

@[simp]
theorem fieldValuedBaseChangeHomeomorph_apply (ψ : A →ₐ[C'] L)
    (x : RingPoints C' (baseChange (Spec.algebraMap C C') X) A) :
    fieldValuedBaseChangeHomeomorph C C' X ψ x = baseChangeRingPointsEquiv C C' A X x := rfl

end FieldBaseChange

end Langlands.AlgebraicGeometry.AlgebraicSpace

open scoped Langlands.Global.FixedModelLocalProduct

namespace Langlands.Global.AdelicSpaceStageCoordinates

open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

section NumberField

variable (K : Type u) [Field K] [NumberField K]
  (S : Finset (FinitePlace K)) (T : AdelicLevelIndexAbove S)

/-- The original enlarged-level fields with the fixed lower coefficient action. -/
scoped instance numberFieldFieldAlgebra (i : NumberFieldLevelFactorIndex K T.val) :
    Algebra ((S : Set (FinitePlace K)).integer K) (NumberFieldLevelField K T.val i) :=
  ((algebraMap ((T.val : Set (FinitePlace K)).integer K)
    (NumberFieldLevelField K T.val i)).comp (numberFieldSIntegersMap K T.property)).toAlgebra

scoped instance numberFieldFieldTower (i : NumberFieldLevelFactorIndex K T.val) :
    IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (NumberFieldLevelField K T.val i) :=
  .of_algebraMap_eq fun _ => rfl

variable (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
  (hsep : IsSeparated X) (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)

/-- An arithmetic stage has the product of its original fixed-base
field-valued coordinate topologies. -/
def numberFieldStageHomeomorph :
    letI := numberFieldSpaceStageTopology K S X T
    letI : ∀ i : NumberFieldLevelFactorIndex K T.val, TopologicalSpace
        (RingPoints ((S : Set (FinitePlace K)).integer K) X
          (NumberFieldLevelFactor K T.val i)) :=
      fun i => fieldValuedPointTopology ((S : Set (FinitePlace K)).integer K) X
        ((numberFieldLevelFieldAlgHom K T.val i).restrictScalars _)
    RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) ≃ₜ
      (∀ i : NumberFieldLevelFactorIndex K T.val,
        RingPoints ((S : Set (FinitePlace K)).integer K) X
          (NumberFieldLevelFactor K T.val i)) := by
  let R := ((S : Set (FinitePlace K)).integer K)
  let R' := ((T.val : Set (FinitePlace K)).integer K)
  let X' := numberFieldSpaceLevelBaseChange K T.property X
  let : TopologicalSpace (RingPoints R X (numberFieldAdeleLevelOver K S T)) :=
    numberFieldSpaceStageTopology K S X T
  let : TopologicalSpace (RingPoints R' X' (numberFieldAdeleLevel K T.val)) :=
    numberFieldSpaceLevelTopology K T.val X'
  let (i : NumberFieldLevelFactorIndex K T.val) :
      TopologicalSpace (RingPoints R' X' (NumberFieldLevelFactor K T.val i)) :=
    fieldValuedPointTopology R' X' (numberFieldLevelFieldAlgHom K T.val i)
  let (i : NumberFieldLevelFactorIndex K T.val) :
      TopologicalSpace (RingPoints R X (NumberFieldLevelFactor K T.val i)) :=
    fieldValuedPointTopology R X ((numberFieldLevelFieldAlgHom K T.val i).restrictScalars R)
  let H := (numberFieldSpaceStageEquiv K S X T).toHomeomorphOfIsInducing ⟨rfl⟩
  exact (H.trans
    (coordinatePointHomeomorph (NumberFieldLevelFactor K T.val) (NumberFieldLevelField K T.val)
      (numberFieldLevelFieldAlgHom K T.val) (numberFieldLevelFactorAlgHom K T.val) X'
      (numberFieldSpaceLevelPoints K T.val X' hsep.baseChange hft.baseChange))).trans
    (Homeomorph.piCongrRight fun i =>
      fieldValuedBaseChangeHomeomorph R R' X (numberFieldLevelFieldAlgHom K T.val i))

@[simp]
theorem numberFieldStageHomeomorph_apply
    (x : RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
    (i : NumberFieldLevelFactorIndex K T.val) :
    numberFieldStageHomeomorph K S T X hsep hft x i =
      RingPoints.changeRing
        ((Pi.evalAlgHom ((S : Set (FinitePlace K)).integer K)
          (NumberFieldLevelFactor K T.val) i).comp
          (FixedModelLocalProduct.numberFieldFactorAlgEquiv K S T).toAlgHom) x := by
  let : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val) :=
    inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T))
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val) :=
    .of_algebraMap_eq fun _ => rfl
  change baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (NumberFieldLevelFactor K T.val i) X
      (RingPoints.changeRing (numberFieldLevelFactorAlgHom K T.val i)
        (numberFieldSpaceStageEquiv K S X T x)) = _
  rw [baseChangeRingPointsEquiv_changeRing]
  have hcancel : baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val) X
      (numberFieldSpaceStageEquiv K S X T x) = x :=
    (baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) X).apply_symm_apply x
  rw [hcancel]
  rfl

end NumberField

end Langlands.Global.AdelicSpaceStageCoordinates
