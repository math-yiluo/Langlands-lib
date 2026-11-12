import Langlands.Global.AdelicSpacePointsProof

/-!
# Enlarging the initial set of a spread

Conrad, printed p.17: the topology on the adelic points of a separated algebraic space of finite
type over a global field does not depend on the model. This module proves one step: the base
change `X_V` of a model `X` over the `S`-integers to the `V`-integers, for `S ⊆ V`, gives the
same topology. The adelic points of `X` and of `X_V` are identified by
`baseChangeRingPointsEquiv`. At a level `T ⊇ V` this identification is the iterated base change
isomorphism `(X_V)_T ≅ X_T` on level topologies, and the levels `T ⊇ V` are cofinal.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeSpacePointComparison

namespace Langlands.Global

namespace AdelicSpaceSpreadInitialSet

open AdelicSpaceLevelTopologyProof AdelicSpacePointMapsProof AdelicSpacePointStagesProof
  AdelicSpacePointsProof

section NumberField

variable (K : Type u) [Field K] [NumberField K] {S V : Finset (FinitePlace K)} (hSV : S ⊆ V)
  (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))

/-- A level above `V` as a level above `S`. -/
abbrev numberFieldLift (T : AdelicLevelIndexAbove V) : AdelicLevelIndexAbove S :=
  ⟨T.val, hSV.trans T.property⟩

/-- The generic fibre of the base change to the `V`-integers is the generic fibre. -/
def numberFieldGenericFiberIso :
    numberFieldSpaceGenericFiber K V (numberFieldSpaceLevelBaseChange K hSV X) ≅
      numberFieldSpaceGenericFiber K S X :=
  BaseChangeComparison.compIso _ _ _ (by rw [← Spec.map_comp]; rfl) X

/-- The points of the base change at a level above `V` are the points of `X` at that level. -/
def numberFieldStageEquiv (T : AdelicLevelIndexAbove V) :
    RingPoints ((V : Set (FinitePlace K)).integer K) (numberFieldSpaceLevelBaseChange K hSV X)
        (numberFieldAdeleLevelOver K V T) ≃
      RingPoints ((S : Set (FinitePlace K)).integer K) X
        (numberFieldAdeleLevelOver K S (numberFieldLift K hSV T)) := by
  letI : Algebra ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K hSV).toAlgebra
  letI : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K V T) :=
    inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S (numberFieldLift K hSV T)))
  letI : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K V T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
    ((V : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K V T) X

/-- The adelic points of the base change are the adelic points of `X`. -/
def numberFieldPointsEquiv :
    NumberFieldSpaceAdelePoints K V (numberFieldSpaceLevelBaseChange K hSV X) ≃
      NumberFieldSpaceAdelePoints K S X := by
  letI : Algebra ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K hSV).toAlgebra
  letI : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K V) :=
    inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S))
  letI : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K)
      (numberFieldAdeleOver K V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
    ((V : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K V) X

/-- The iterated base change `(X_V)_T ≅ X_T`. -/
def numberFieldTowerIso (T : AdelicLevelIndexAbove V) :
    numberFieldSpaceLevelBaseChange K T.property (numberFieldSpaceLevelBaseChange K hSV X) ≅
      numberFieldSpaceLevelBaseChange K (hSV.trans T.property) X :=
  BaseChangeComparison.compIso _ _ _ (by rw [← Spec.map_comp]; rfl) X

/-- Under the stage identifications, the identification of stages is the iterated base change
isomorphism. -/
theorem numberField_stage_comm (T : AdelicLevelIndexAbove V)
    (q : RingPoints ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldSpaceLevelBaseChange K T.property (numberFieldSpaceLevelBaseChange K hSV X))
      (numberFieldAdeleLevel K T.val)) :
    numberFieldStageEquiv K hSV X T
        ((numberFieldSpaceStageEquiv K V (numberFieldSpaceLevelBaseChange K hSV X) T).symm q) =
      (numberFieldSpaceStageEquiv K S X (numberFieldLift K hSV T)).symm
        (RingPoints.map (numberFieldTowerIso K hSV X T).hom q) := by
  let _ : Algebra ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K hSV).toAlgebra
  let _ : Algebra ((V : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let _ : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K (hSV.trans T.property)).toAlgebra
  have : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra ((V : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val) :=
    ((algebraMap ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val)).comp
      (algebraMap ((V : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K))).toAlgebra
  let _ : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val) :=
    ((algebraMap ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val)).comp
      (algebraMap ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K))).toAlgebra
  have : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevel K T.val) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ((V : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevel K T.val) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevel K T.val) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (baseChangeRingPointsEquiv_towerIso ((S : Set (FinitePlace K)).integer K)
    ((V : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevel K T.val) X q).symm

/-- The stage maps are compatible with the identifications. -/
theorem numberField_points_comm (T : AdelicLevelIndexAbove V)
    (p : RingPoints ((V : Set (FinitePlace K)).integer K) (numberFieldSpaceLevelBaseChange K hSV X)
      (numberFieldAdeleLevelOver K V T)) :
    numberFieldPointsEquiv K hSV X
        (numberFieldSpaceStageMap K V (numberFieldSpaceLevelBaseChange K hSV X) T p) =
      numberFieldSpaceStageMap K S X (numberFieldLift K hSV T) (numberFieldStageEquiv K hSV X T p) := by
  change X.pullback _ (X.pullback _ p) = X.pullback _ (X.pullback _ p)
  refine (pullback_comp X _ _ p).symm.trans (Eq.trans ?_ (pullback_comp X _ _ p))
  apply BaseChangeComparison.pullback_congr_left
  simp
  rfl

/-- The identification of stages is a homeomorphism. -/
theorem numberField_stage_isHomeomorph (T : AdelicLevelIndexAbove V) :
    @IsHomeomorph _ _ (numberFieldSpaceStageTopology K V (numberFieldSpaceLevelBaseChange K hSV X) T)
      (numberFieldSpaceStageTopology K S X (numberFieldLift K hSV T))
      (numberFieldStageEquiv K hSV X T) := by
  let XV := numberFieldSpaceLevelBaseChange K hSV X
  let _ := numberFieldSpaceStageTopology K V XV T
  let _ := numberFieldSpaceStageTopology K S X (numberFieldLift K hSV T)
  let _ := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property XV)
  let _ := numberFieldSpaceLevelTopology K T.val
    (numberFieldSpaceLevelBaseChange K (hSV.trans T.property) X)
  have h₁ := numberField_stageEquiv_isHomeomorph K V (X := XV) T
  have h₂ := numberField_stageEquiv_isHomeomorph K S (X := X) (numberFieldLift K hSV T)
  have hiso := isHomeomorph_coordinate_iso (A := numberFieldAdeleLevel K T.val)
    (NumberFieldLevelFactor K T.val) (NumberFieldLevelField K T.val)
    (numberFieldLevelFieldAlgHom K T.val) (numberFieldLevelFactorAlgHom K T.val)
    (numberFieldTowerIso K hSV X T)
  have h₂s : IsHomeomorph (numberFieldSpaceStageEquiv K S X (numberFieldLift K hSV T)).symm :=
    (numberFieldSpaceStageEquiv K S X (numberFieldLift K hSV T)).symm.isHomeomorph_iff.mpr
      ⟨(numberFieldSpaceStageEquiv K S X (numberFieldLift K hSV T)).continuous_symm_iff.mpr
        h₂.isOpenMap, h₂.continuous⟩
  have hfun : (numberFieldStageEquiv K hSV X T : _ → _) =
      (numberFieldSpaceStageEquiv K S X (numberFieldLift K hSV T)).symm ∘
        (RingPoints.mapEquiv (numberFieldTowerIso K hSV X T) ∘
          numberFieldSpaceStageEquiv K V XV T) := by
    funext p
    have h := numberField_stage_comm K hSV X T (numberFieldSpaceStageEquiv K V XV T p)
    rwa [Equiv.symm_apply_apply] at h
  rw [hfun]
  exact h₂s.comp (hiso.comp h₁)

/-- **Enlarging the initial set**: the identification of adelic points is a homeomorphism. -/
theorem numberField_pointsEquiv_isHomeomorph (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X) :
    @IsHomeomorph _ _ (numberFieldSpaceAdelePointTopology K V (numberFieldSpaceLevelBaseChange K hSV X))
      (numberFieldSpaceAdelePointTopology K S X) (numberFieldPointsEquiv K hSV X) := by
  let XV := numberFieldSpaceLevelBaseChange K hSV X
  let _ := numberFieldSpaceAdelePointTopology K V XV
  let _ := numberFieldSpaceAdelePointTopology K S X
  let _ (T : AdelicLevelIndexAbove V) := numberFieldSpaceStageTopology K V XV T
  let _ (T : AdelicLevelIndexAbove S) := numberFieldSpaceStageTopology K S X T
  have hψ := numberField_stage_isHomeomorph K hSV X
  have hc : Continuous (numberFieldPointsEquiv K hSV X) := by
    refine (Topology.FinalStage.continuous_final_iff (τ := numberFieldSpaceStageTopology K V XV)
      (numberFieldSpaceStageMap K V XV)).mpr fun T => ?_
    have : (numberFieldPointsEquiv K hSV X : _ → _) ∘ numberFieldSpaceStageMap K V XV T =
        numberFieldSpaceStageMap K S X (numberFieldLift K hSV T) ∘ numberFieldStageEquiv K hSV X T :=
      funext (numberField_points_comm K hSV X T)
    rw [this]
    exact (Topology.FinalStage.continuous_stage (τ := numberFieldSpaceStageTopology K S X)
      (numberFieldSpaceStageMap K S X) (numberFieldLift K hSV T)).comp (hψ T).continuous
  have hc' : Continuous (numberFieldPointsEquiv K hSV X).symm := by
    refine (Topology.FinalStage.continuous_final_iff (τ := numberFieldSpaceStageTopology K S X)
      (numberFieldSpaceStageMap K S X)).mpr fun T => ?_
    classical
    let W : AdelicLevelIndexAbove V := ⟨T.val ∪ V, Finset.subset_union_right⟩
    have h : T ≤ numberFieldLift K hSV W := Finset.subset_union_left
    have hsymm : Continuous (numberFieldStageEquiv K hSV X W).symm :=
      (numberFieldStageEquiv K hSV X W).continuous_symm_iff.mpr (hψ W).isOpenMap
    have : ((numberFieldPointsEquiv K hSV X).symm : _ → _) ∘ numberFieldSpaceStageMap K S X T =
        numberFieldSpaceStageMap K V XV W ∘ ((numberFieldStageEquiv K hSV X W).symm ∘
          RingPoints.changeRing (numberFieldAdeleLevelOverMap K S h).hom) := by
      funext x
      simp only [Function.comp_apply]
      rw [← numberField_stageMap_transition K S h x, Equiv.symm_apply_eq,
        numberField_points_comm, Equiv.apply_symm_apply]
    rw [this]
    exact (Topology.FinalStage.continuous_stage (τ := numberFieldSpaceStageTopology K V XV)
      (numberFieldSpaceStageMap K V XV) W).comp
        (hsymm.comp (numberField_stage_transition K S hX hft h).continuous)
  exact (Homeomorph.mk (numberFieldPointsEquiv K hSV X) hc hc').isHomeomorph

/-- The identification of adelic points is compatible with the generic fibres. -/
theorem numberField_genericFiber_comm
    (z : NumberFieldSpaceFieldAdelePoints K
      (numberFieldSpaceGenericFiber K V (numberFieldSpaceLevelBaseChange K hSV X))) :
    (numberFieldSpaceGenericFiberEquiv K S X).symm
        (RingPoints.map (numberFieldGenericFiberIso K hSV X).hom z) =
      numberFieldPointsEquiv K hSV X
        ((numberFieldSpaceGenericFiberEquiv K V (numberFieldSpaceLevelBaseChange K hSV X)).symm z) := by
  let algSV : Algebra ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K hSV).toAlgebra
  let algVK : Algebra ((V : Set (FinitePlace K)).integer K) K :=
    ((V : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let algSK : Algebra ((S : Set (FinitePlace K)).integer K) K :=
    ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  have : @IsScalarTower ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K) K
      algSV.toSMul algVK.toSMul algSK.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSV algVK algSK fun _ => rfl
  let algKB : Algebra K (Adeles K) := inferInstance
  let algVB : Algebra ((V : Set (FinitePlace K)).integer K) (Adeles K) :=
    inferInstanceAs (Algebra ((V : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K V))
  let algSB : Algebra ((S : Set (FinitePlace K)).integer K) (Adeles K) :=
    inferInstanceAs (Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S))
  have : @IsScalarTower ((S : Set (FinitePlace K)).integer K) ((V : Set (FinitePlace K)).integer K)
      (Adeles K) algSV.toSMul algVB.toSMul algSB.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSV algVB algSB fun _ => rfl
  have : @IsScalarTower ((V : Set (FinitePlace K)).integer K) K (Adeles K)
      algVK.toSMul algKB.toSMul algVB.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algVK algKB algVB fun _ => rfl
  have : @IsScalarTower ((S : Set (FinitePlace K)).integer K) K (Adeles K)
      algSK.toSMul algKB.toSMul algSB.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSK algKB algSB fun _ => rfl
  let _ := algSV
  let _ := algVK
  let _ := algSK
  let _ := algKB
  let _ := algVB
  let _ := algSB
  exact baseChangeRingPointsEquiv_towerIso ((S : Set (FinitePlace K)).integer K)
    ((V : Set (FinitePlace K)).integer K) K (Adeles K) X z

/-- The identification of adelic points is compatible with the spread identifications. -/
theorem numberField_spreadEquiv_comm (Y : AlgebraicSpace (Spec (CommRingCat.of K)))
    (e : numberFieldSpaceGenericFiber K S X ≅ Y)
    (y : NumberFieldSpaceAdelePoints K V (numberFieldSpaceLevelBaseChange K hSV X)) :
    numberFieldSpaceSpreadEquiv K S X Y e (numberFieldPointsEquiv K hSV X y) =
      numberFieldSpaceSpreadEquiv K V (numberFieldSpaceLevelBaseChange K hSV X) Y
        (numberFieldGenericFiberIso K hSV X ≪≫ e) y := by
  obtain ⟨z, rfl⟩ := (numberFieldSpaceGenericFiberEquiv K V
    (numberFieldSpaceLevelBaseChange K hSV X)).symm.surjective y
  rw [numberFieldSpaceSpreadEquiv, numberFieldSpaceSpreadEquiv, Equiv.trans_apply,
    Equiv.trans_apply, ← numberField_genericFiber_comm, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rfl

/-- **Enlarging the initial set of a spread**, number fields: the base change of a separated
model of finite type to the `V`-integers, with the induced isomorphism of generic fibres, defines
the same topology on adelic points. -/
theorem numberField_spreadTopology_eq (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (Y : AlgebraicSpace (Spec (CommRingCat.of K))) (e : numberFieldSpaceGenericFiber K S X ≅ Y) :
    numberFieldSpaceSpreadTopology K S X Y e =
      numberFieldSpaceSpreadTopology K V (numberFieldSpaceLevelBaseChange K hSV X) Y
        (numberFieldGenericFiberIso K hSV X ≪≫ e) := by
  have h := numberField_pointsEquiv_isHomeomorph K hSV X hX hft
  have hfun : ((numberFieldSpaceSpreadEquiv K V (numberFieldSpaceLevelBaseChange K hSV X) Y
      (numberFieldGenericFiberIso K hSV X ≪≫ e)).symm : _ → _) =
      (numberFieldPointsEquiv K hSV X).symm ∘ (numberFieldSpaceSpreadEquiv K S X Y e).symm := by
    funext w
    rw [Equiv.symm_apply_eq, Function.comp_apply, ← numberField_spreadEquiv_comm,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hind : TopologicalSpace.induced (numberFieldPointsEquiv K hSV X).symm
      (numberFieldSpaceAdelePointTopology K V (numberFieldSpaceLevelBaseChange K hSV X)) =
      numberFieldSpaceAdelePointTopology K S X := by
    let _ := numberFieldSpaceAdelePointTopology K V (numberFieldSpaceLevelBaseChange K hSV X)
    let _ := numberFieldSpaceAdelePointTopology K S X
    exact (Homeomorph.mk (numberFieldPointsEquiv K hSV X) h.continuous
      ((numberFieldPointsEquiv K hSV X).continuous_symm_iff.mpr h.isOpenMap)).symm.isInducing.eq_induced.symm
  rw [numberFieldSpaceSpreadTopology, numberFieldSpaceSpreadTopology, hfun, ← induced_compose, hind]

end NumberField

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F] {S V : Finset (AlgebraicCurve.Place k F)}
  (hSV : S ⊆ V) (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))

/-- A level above `V` as a level above `S`. -/
abbrev curveLift (T : AdelicLevelIndexAbove V) : AdelicLevelIndexAbove S :=
  ⟨T.val, hSV.trans T.property⟩

/-- The generic fibre of the base change to the `V`-integers is the generic fibre. -/
def curveGenericFiberIso :
    curvePlaceSpaceGenericFiber k F V (curvePlaceSpaceLevelBaseChange k F hSV X) ≅
      curvePlaceSpaceGenericFiber k F S X :=
  BaseChangeComparison.compIso _ _ _ (by rw [← Spec.map_comp]; rfl) X

/-- The points of the base change at a level above `V` are the points of `X` at that level. -/
def curveStageEquiv (T : AdelicLevelIndexAbove V) :
    RingPoints (curvePlaceSIntegers k F V) (curvePlaceSpaceLevelBaseChange k F hSV X)
        (curvePlaceAdeleLevelOver k F V T) ≃
      RingPoints (curvePlaceSIntegers k F S) X
        (curvePlaceAdeleLevelOver k F S (curveLift k F hSV T)) := by
  letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V) :=
    (curvePlaceSIntegersMap k F hSV).toAlgebra
  letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleLevelOver k F V T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevelOver k F S (curveLift k F hSV T)))
  letI : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V)
      (curvePlaceAdeleLevelOver k F V T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F V) (curvePlaceAdeleLevelOver k F V T) X

/-- The adelic points of the base change are the adelic points of `X`. -/
def curvePointsEquiv :
    CurvePlaceSpaceAdelePoints k F V (curvePlaceSpaceLevelBaseChange k F hSV X) ≃
      CurvePlaceSpaceAdelePoints k F S X := by
  letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V) :=
    (curvePlaceSIntegersMap k F hSV).toAlgebra
  letI : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F V) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S))
  letI : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V)
      (curvePlaceAdeleOver k F V) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F V) (curvePlaceAdeleOver k F V) X

/-- The iterated base change `(X_V)_T ≅ X_T`. -/
def curveTowerIso (T : AdelicLevelIndexAbove V) :
    curvePlaceSpaceLevelBaseChange k F T.property (curvePlaceSpaceLevelBaseChange k F hSV X) ≅
      curvePlaceSpaceLevelBaseChange k F (hSV.trans T.property) X :=
  BaseChangeComparison.compIso _ _ _ (by rw [← Spec.map_comp]; rfl) X

set_option maxHeartbeats 1000000 in
omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- Under the stage identifications, the identification of stages is the iterated base change
isomorphism. -/
theorem curve_stage_comm (T : AdelicLevelIndexAbove V)
    (q : RingPoints (curvePlaceSIntegers k F T.val)
      (curvePlaceSpaceLevelBaseChange k F T.property (curvePlaceSpaceLevelBaseChange k F hSV X))
      (curvePlaceAdeleLevel k F T.val)) :
    curveStageEquiv k F hSV X T
        ((curvePlaceSpaceStageEquiv k F V (curvePlaceSpaceLevelBaseChange k F hSV X) T).symm q) =
      (curvePlaceSpaceStageEquiv k F S X (curveLift k F hSV T)).symm
        (RingPoints.map (curveTowerIso k F hSV X T).hom q) := by
  let _ : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V) :=
    (curvePlaceSIntegersMap k F hSV).toAlgebra
  let _ : Algebra (curvePlaceSIntegers k F V) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let _ : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F (hSV.trans T.property)).toAlgebra
  have : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V)
      (curvePlaceSIntegers k F T.val) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra (curvePlaceSIntegers k F V) (curvePlaceAdeleLevel k F T.val) :=
    ((algebraMap (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val)).comp
      (algebraMap (curvePlaceSIntegers k F V) (curvePlaceSIntegers k F T.val))).toAlgebra
  let _ : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleLevel k F T.val) :=
    ((algebraMap (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val)).comp
      (algebraMap (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val))).toAlgebra
  have : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V)
      (curvePlaceAdeleLevel k F T.val) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (curvePlaceSIntegers k F V) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevel k F T.val) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevel k F T.val) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact (baseChangeRingPointsEquiv_towerIso (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F V) (curvePlaceSIntegers k F T.val)
    (curvePlaceAdeleLevel k F T.val) X q).symm

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- The stage maps are compatible with the identifications. -/
theorem curve_points_comm (T : AdelicLevelIndexAbove V)
    (p : RingPoints (curvePlaceSIntegers k F V) (curvePlaceSpaceLevelBaseChange k F hSV X)
      (curvePlaceAdeleLevelOver k F V T)) :
    curvePointsEquiv k F hSV X
        (curvePlaceSpaceStageMap k F V (curvePlaceSpaceLevelBaseChange k F hSV X) T p) =
      curvePlaceSpaceStageMap k F S X (curveLift k F hSV T) (curveStageEquiv k F hSV X T p) := by
  change X.pullback _ (X.pullback _ p) = X.pullback _ (X.pullback _ p)
  refine (pullback_comp X _ _ p).symm.trans (Eq.trans ?_ (pullback_comp X _ _ p))
  apply BaseChangeComparison.pullback_congr_left
  simp
  rfl

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- The identification of stages is a homeomorphism. -/
theorem curve_stage_isHomeomorph (T : AdelicLevelIndexAbove V) :
    @IsHomeomorph _ _ (curvePlaceSpaceStageTopology k F V (curvePlaceSpaceLevelBaseChange k F hSV X) T)
      (curvePlaceSpaceStageTopology k F S X (curveLift k F hSV T))
      (curveStageEquiv k F hSV X T) := by
  let XV := curvePlaceSpaceLevelBaseChange k F hSV X
  let _ := curvePlaceSpaceStageTopology k F V XV T
  let _ := curvePlaceSpaceStageTopology k F S X (curveLift k F hSV T)
  let _ := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property XV)
  let _ := curvePlaceSpaceLevelTopology k F T.val
    (curvePlaceSpaceLevelBaseChange k F (hSV.trans T.property) X)
  have h₁ := curve_stageEquiv_isHomeomorph k F V (X := XV) T
  have h₂ := curve_stageEquiv_isHomeomorph k F S (X := X) (curveLift k F hSV T)
  have hiso := isHomeomorph_coordinate_iso (A := curvePlaceAdeleLevel k F T.val)
    (CurvePlaceLevelFactor k F T.val) (CurvePlaceLevelField k F T.val)
    (curvePlaceLevelFieldAlgHom k F T.val) (curvePlaceLevelFactorAlgHom k F T.val)
    (curveTowerIso k F hSV X T)
  have h₂s : IsHomeomorph (curvePlaceSpaceStageEquiv k F S X (curveLift k F hSV T)).symm :=
    (curvePlaceSpaceStageEquiv k F S X (curveLift k F hSV T)).symm.isHomeomorph_iff.mpr
      ⟨(curvePlaceSpaceStageEquiv k F S X (curveLift k F hSV T)).continuous_symm_iff.mpr
        h₂.isOpenMap, h₂.continuous⟩
  have hfun : (curveStageEquiv k F hSV X T : _ → _) =
      (curvePlaceSpaceStageEquiv k F S X (curveLift k F hSV T)).symm ∘
        (RingPoints.mapEquiv (curveTowerIso k F hSV X T) ∘
          curvePlaceSpaceStageEquiv k F V XV T) := by
    funext p
    have h := curve_stage_comm k F hSV X T (curvePlaceSpaceStageEquiv k F V XV T p)
    rwa [Equiv.symm_apply_apply] at h
  rw [hfun]
  exact h₂s.comp (hiso.comp h₁)

/-- **Enlarging the initial set**: the identification of adelic points is a homeomorphism. -/
theorem curve_pointsEquiv_isHomeomorph (hS : S.Nonempty) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X) :
    @IsHomeomorph _ _ (curvePlaceSpaceAdelePointTopology k F V (curvePlaceSpaceLevelBaseChange k F hSV X))
      (curvePlaceSpaceAdelePointTopology k F S X) (curvePointsEquiv k F hSV X) := by
  let XV := curvePlaceSpaceLevelBaseChange k F hSV X
  let _ := curvePlaceSpaceAdelePointTopology k F V XV
  let _ := curvePlaceSpaceAdelePointTopology k F S X
  let _ (T : AdelicLevelIndexAbove V) := curvePlaceSpaceStageTopology k F V XV T
  let _ (T : AdelicLevelIndexAbove S) := curvePlaceSpaceStageTopology k F S X T
  have hψ := curve_stage_isHomeomorph k F hSV X
  have hc : Continuous (curvePointsEquiv k F hSV X) := by
    refine (Topology.FinalStage.continuous_final_iff (τ := curvePlaceSpaceStageTopology k F V XV)
      (curvePlaceSpaceStageMap k F V XV)).mpr fun T => ?_
    have : (curvePointsEquiv k F hSV X : _ → _) ∘ curvePlaceSpaceStageMap k F V XV T =
        curvePlaceSpaceStageMap k F S X (curveLift k F hSV T) ∘ curveStageEquiv k F hSV X T :=
      funext (curve_points_comm k F hSV X T)
    rw [this]
    exact (Topology.FinalStage.continuous_stage (τ := curvePlaceSpaceStageTopology k F S X)
      (curvePlaceSpaceStageMap k F S X) (curveLift k F hSV T)).comp (hψ T).continuous
  have hc' : Continuous (curvePointsEquiv k F hSV X).symm := by
    refine (Topology.FinalStage.continuous_final_iff (τ := curvePlaceSpaceStageTopology k F S X)
      (curvePlaceSpaceStageMap k F S X)).mpr fun T => ?_
    classical
    let W : AdelicLevelIndexAbove V := ⟨T.val ∪ V, Finset.subset_union_right⟩
    have h : T ≤ curveLift k F hSV W := Finset.subset_union_left
    have hsymm : Continuous (curveStageEquiv k F hSV X W).symm :=
      (curveStageEquiv k F hSV X W).continuous_symm_iff.mpr (hψ W).isOpenMap
    have : ((curvePointsEquiv k F hSV X).symm : _ → _) ∘ curvePlaceSpaceStageMap k F S X T =
        curvePlaceSpaceStageMap k F V XV W ∘ ((curveStageEquiv k F hSV X W).symm ∘
          RingPoints.changeRing (curvePlaceAdeleLevelOverMap k F S h).hom) := by
      funext x
      simp only [Function.comp_apply]
      rw [← curve_stageMap_transition k F S h x, Equiv.symm_apply_eq,
        curve_points_comm, Equiv.apply_symm_apply]
    rw [this]
    exact (Topology.FinalStage.continuous_stage (τ := curvePlaceSpaceStageTopology k F V XV)
      (curvePlaceSpaceStageMap k F V XV) W).comp
        (hsymm.comp (curve_stage_transition k F S hX hS hft h).continuous)
  exact (Homeomorph.mk (curvePointsEquiv k F hSV X) hc hc').isHomeomorph

/-- The identification of adelic points is compatible with the generic fibres. -/
theorem curve_genericFiber_comm
    (z : CurvePlaceSpaceFieldAdelePoints k F
      (curvePlaceSpaceGenericFiber k F V (curvePlaceSpaceLevelBaseChange k F hSV X))) :
    (curvePlaceSpaceGenericFiberEquiv k F S X).symm
        (RingPoints.map (curveGenericFiberIso k F hSV X).hom z) =
      curvePointsEquiv k F hSV X
        ((curvePlaceSpaceGenericFiberEquiv k F V (curvePlaceSpaceLevelBaseChange k F hSV X)).symm z) := by
  let algSV : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V) :=
    (curvePlaceSIntegersMap k F hSV).toAlgebra
  let algVK : Algebra (curvePlaceSIntegers k F V) F :=
    (curvePlaceSIntegers k F V).subtype.toAlgebra
  let algSK : Algebra (curvePlaceSIntegers k F S) F :=
    (curvePlaceSIntegers k F S).subtype.toAlgebra
  have : @IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V) F
      algSV.toSMul algVK.toSMul algSK.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSV algVK algSK fun _ => rfl
  let algKB : Algebra F (CurvePlaceAdeleRing k F) := inferInstance
  let algVB : Algebra (curvePlaceSIntegers k F V) (CurvePlaceAdeleRing k F) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F V) (curvePlaceAdeleOver k F V))
  let algSB : Algebra (curvePlaceSIntegers k F S) (CurvePlaceAdeleRing k F) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S))
  have : @IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F V)
      (CurvePlaceAdeleRing k F) algSV.toSMul algVB.toSMul algSB.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSV algVB algSB fun x =>
      (curvePlaceAdeleLevelDiagonal_eq k F S x).trans
        (curvePlaceAdeleLevelDiagonal_eq k F V (curvePlaceSIntegersMap k F hSV x)).symm
  have : @IsScalarTower (curvePlaceSIntegers k F V) F (CurvePlaceAdeleRing k F)
      algVK.toSMul algKB.toSMul algVB.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algVK algKB algVB
      (curvePlaceAdeleLevelDiagonal_eq k F V)
  have : @IsScalarTower (curvePlaceSIntegers k F S) F (CurvePlaceAdeleRing k F)
      algSK.toSMul algKB.toSMul algSB.toSMul :=
    @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSK algKB algSB
      (curvePlaceAdeleLevelDiagonal_eq k F S)
  let _ := algSV
  let _ := algVK
  let _ := algSK
  let _ := algKB
  let _ := algVB
  let _ := algSB
  exact baseChangeRingPointsEquiv_towerIso (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F V) F (CurvePlaceAdeleRing k F) X z

/-- The identification of adelic points is compatible with the spread identifications. -/
theorem curve_spreadEquiv_comm (Y : AlgebraicSpace (Spec (CommRingCat.of F)))
    (e : curvePlaceSpaceGenericFiber k F S X ≅ Y)
    (y : CurvePlaceSpaceAdelePoints k F V (curvePlaceSpaceLevelBaseChange k F hSV X)) :
    curvePlaceSpaceSpreadEquiv k F S X Y e (curvePointsEquiv k F hSV X y) =
      curvePlaceSpaceSpreadEquiv k F V (curvePlaceSpaceLevelBaseChange k F hSV X) Y
        (curveGenericFiberIso k F hSV X ≪≫ e) y := by
  obtain ⟨z, rfl⟩ := (curvePlaceSpaceGenericFiberEquiv k F V
    (curvePlaceSpaceLevelBaseChange k F hSV X)).symm.surjective y
  rw [curvePlaceSpaceSpreadEquiv, curvePlaceSpaceSpreadEquiv, Equiv.trans_apply,
    Equiv.trans_apply, ← curve_genericFiber_comm, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply]
  rfl

/-- **Enlarging the initial set of a spread**, global function fields: the base change of a separated
model of finite type to the `V`-integers, with the induced isomorphism of generic fibres, defines
the same topology on adelic points. -/
theorem curve_spreadTopology_eq (hS : S.Nonempty) (hX : IsSeparated X)
    (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (Y : AlgebraicSpace (Spec (CommRingCat.of F))) (e : curvePlaceSpaceGenericFiber k F S X ≅ Y) :
    curvePlaceSpaceSpreadTopology k F S X Y e =
      curvePlaceSpaceSpreadTopology k F V (curvePlaceSpaceLevelBaseChange k F hSV X) Y
        (curveGenericFiberIso k F hSV X ≪≫ e) := by
  have h := curve_pointsEquiv_isHomeomorph k F hSV X hS hX hft
  have hfun : ((curvePlaceSpaceSpreadEquiv k F V (curvePlaceSpaceLevelBaseChange k F hSV X) Y
      (curveGenericFiberIso k F hSV X ≪≫ e)).symm : _ → _) =
      (curvePointsEquiv k F hSV X).symm ∘ (curvePlaceSpaceSpreadEquiv k F S X Y e).symm := by
    funext w
    rw [Equiv.symm_apply_eq, Function.comp_apply, ← curve_spreadEquiv_comm,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hind : TopologicalSpace.induced (curvePointsEquiv k F hSV X).symm
      (curvePlaceSpaceAdelePointTopology k F V (curvePlaceSpaceLevelBaseChange k F hSV X)) =
      curvePlaceSpaceAdelePointTopology k F S X := by
    let _ := curvePlaceSpaceAdelePointTopology k F V (curvePlaceSpaceLevelBaseChange k F hSV X)
    let _ := curvePlaceSpaceAdelePointTopology k F S X
    exact (Homeomorph.mk (curvePointsEquiv k F hSV X) h.continuous
      ((curvePointsEquiv k F hSV X).continuous_symm_iff.mpr h.isOpenMap)).symm.isInducing.eq_induced.symm
  rw [curvePlaceSpaceSpreadTopology, curvePlaceSpaceSpreadTopology, hfun, ← induced_compose, hind]

end Curve

end AdelicSpaceSpreadInitialSet

end Langlands.Global
