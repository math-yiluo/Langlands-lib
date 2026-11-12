import Langlands.Global.AdelicSpacePointMapsProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeSpacePointComparison

/-!
# The stages of adelic points of separated algebraic spaces

Conrad, printed p.17: for a separated algebraic space `X` of finite type over the `S`-integers
of a global field, the stage maps `X(A_T) → X(𝔸)` from the levels are open embeddings for the
final topology. Under the stage identifications, a change of stage `T ≤ T'` is the change of
level of the base change of `X` to the `T`-integers, followed by an iterated base change
isomorphism, so it is an open embedding. The stage maps are injective, and the stages form a
directed system.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps
open Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeSpacePointComparison

namespace Langlands.Global

namespace AdelicSpacePointStagesProof

open AdelicSpaceLevelTopologyProof AdelicSpacePointMapsProof

/-- The stages above a finite set form a directed system. -/
instance isDirected_levelIndex {ι : Type u} (S : Finset ι) :
    IsDirected (AdelicLevelIndexAbove S) (· ≤ ·) := by
  classical
  exact ⟨fun T U => ⟨⟨T.val ∪ U.val, T.property.trans Finset.subset_union_left⟩,
    Finset.subset_union_left, Finset.subset_union_right⟩⟩

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
  {X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- **Change of stage**, number fields: an open embedding. -/
theorem numberField_stage_transition (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    {T T' : AdelicLevelIndexAbove S} (h : T ≤ T') :
    @IsOpenEmbedding _ _ (numberFieldSpaceStageTopology K S X T)
      (numberFieldSpaceStageTopology K S X T')
      (RingPoints.changeRing (numberFieldAdeleLevelOverMap K S h).hom) := by
  have hTT' : T.val ⊆ T'.val := h
  have fST : Fact (S ⊆ T.val) := ⟨T.property⟩
  have fTT' : Fact (T.val ⊆ T'.val) := ⟨hTT'⟩
  have fST' : Fact (S ⊆ T'.val) := ⟨T'.property⟩
  let XT := numberFieldSpaceLevelBaseChange K T.property X
  have hXT : IsSeparated XT := hX.baseChange
  have hftT : FiniteTypeOverRing ((T.val : Set (FinitePlace K)).integer K) XT :=
    finiteTypeOverRing_baseChange _ hft
  have hlev := numberField_transition (T := T'.val) XT hXT hftT
  let _ : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    algST K
  let _ : Algebra ((T.val : Set (FinitePlace K)).integer K)
      ((T'.val : Set (FinitePlace K)).integer K) := algST K
  let _ : Algebra ((S : Set (FinitePlace K)).integer K)
      ((T'.val : Set (FinitePlace K)).integer K) := algST K
  have : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) ((T'.val : Set (FinitePlace K)).integer K) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e := towerIso ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
    ((T'.val : Set (FinitePlace K)).integer K) X
  have hiso := isHomeomorph_coordinate_iso (A := numberFieldAdeleLevel K T'.val)
    (NumberFieldLevelFactor K T'.val) (NumberFieldLevelField K T'.val)
    (numberFieldLevelFieldAlgHom K T'.val) (numberFieldLevelFactorAlgHom K T'.val) e
  have h₁ := numberField_stageEquiv_isHomeomorph K S (X := X) T
  have h₄ := numberField_stageEquiv_isHomeomorph K S (X := X) T'
  let _ : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs
      (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  have : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra ((T'.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T') :=
    inferInstanceAs
      (Algebra ((T'.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T'.val))
  have : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T'.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T') :=
    algLevel K
  have : IsScalarTower ((T.val : Set (FinitePlace K)).integer K)
      ((T'.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hpt : ∀ p, numberFieldSpaceStageEquiv K S X T'
      (RingPoints.changeRing (numberFieldAdeleLevelOverMap K S h).hom p) =
      RingPoints.map e.hom (numberFieldSpaceLevelTransition K hTT' XT
        (numberFieldSpaceStageEquiv K S X T p)) := by
    intro p
    change (baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K)
      ((T'.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T') X).symm _ = _
    apply (Equiv.symm_apply_eq _).mpr
    change X.pullback _ p = X.pullback _ (X.pullback _ (X.pullback _ (X.pullback _ p)))
    refine (BaseChangeComparison.pullback_congr_left X (g := _ ≫ _ ≫ _ ≫ _) ?_ p).trans
      ((pullback_comp X _ _ _).trans (congrArg _ ((pullback_comp X _ _ _).trans
        (congrArg _ (pullback_comp X _ _ _)))))
    simp
    rfl
  let _ := numberFieldSpaceStageTopology K S X T
  let _ := numberFieldSpaceStageTopology K S X T'
  let _ := numberFieldSpaceLevelTopology K T.val XT
  let _ := numberFieldSpaceLevelTopology K T'.val (numberFieldSpaceLevelBaseChange K hTT' XT)
  let _ := numberFieldSpaceLevelTopology K T'.val (numberFieldSpaceLevelBaseChange K T'.property X)
  let _ := numberFieldSpaceLevelTopology K T'.val
    (baseChange (Spec.algebraMap ((T.val : Set (FinitePlace K)).integer K)
      ((T'.val : Set (FinitePlace K)).integer K))
      (baseChange (Spec.algebraMap ((S : Set (FinitePlace K)).integer K)
        ((T.val : Set (FinitePlace K)).integer K)) X))
  let _ := numberFieldSpaceLevelTopology K T'.val
    (baseChange (Spec.algebraMap ((S : Set (FinitePlace K)).integer K)
      ((T'.val : Set (FinitePlace K)).integer K)) X)
  have hfun : RingPoints.changeRing (numberFieldAdeleLevelOverMap K S h).hom =
      (numberFieldSpaceStageEquiv K S X T').symm ∘ (RingPoints.map e.hom ∘
        (numberFieldSpaceLevelTransition K hTT' XT ∘ numberFieldSpaceStageEquiv K S X T)) := by
    funext p
    exact ((Equiv.symm_apply_eq _).mpr (hpt p).symm).symm
  have h₄s : IsHomeomorph (numberFieldSpaceStageEquiv K S X T').symm :=
    (numberFieldSpaceStageEquiv K S X T').symm.isHomeomorph_iff.mpr
      ⟨(numberFieldSpaceStageEquiv K S X T').continuous_symm_iff.mpr h₄.isOpenMap, h₄.continuous⟩
  rw [hfun]
  exact h₄s.isOpenEmbedding.comp (hiso.isOpenEmbedding.comp (hlev.comp h₁.isOpenEmbedding))

/-- **Stages are open embeddings**, number fields. -/
theorem numberField_stage_isOpenEmbedding (hX : IsSeparated X)
    (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X) (T : AdelicLevelIndexAbove S) :
    @IsOpenEmbedding _ _ (numberFieldSpaceStageTopology K S X T)
      (numberFieldSpaceAdelePointTopology K S X) (numberFieldSpaceStageMap K S X T) :=
  Topology.FinalStage.isOpenEmbedding_stage (τ := numberFieldSpaceStageTopology K S X)
    (numberFieldSpaceStageMap K S X)
    (fun h => RingPoints.changeRing (numberFieldAdeleLevelOverMap K S h).hom)
    (fun h => numberField_stage_transition K S hX hft h)
    (fun h x => by
      simp only [numberFieldSpaceStageMap, ProductPointsDescent.changeRing_changeRing]
      rfl)
    (fun T => RelativeIntegralPoints.changeRing_injective hX _ (numberField_levelι_injective K S T)) T

end NumberField

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F] [Algebra (RatFunc k) F]
  [IsScalarTower k (RatFunc k) F] [FunctionField k F] (S : Finset (AlgebraicCurve.Place k F))
  {X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- **Change of stage**, global function fields: an open embedding. -/
theorem curve_stage_transition (hX : IsSeparated X)
    (hS : S.Nonempty) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    {T T' : AdelicLevelIndexAbove S} (h : T ≤ T') :
    @IsOpenEmbedding _ _ (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceStageTopology k F S X T')
      (RingPoints.changeRing (curvePlaceAdeleLevelOverMap k F S h).hom) := by
  have hTT' : T.val ⊆ T'.val := h
  have fST : Fact (S ⊆ T.val) := ⟨T.property⟩
  have fTT' : Fact (T.val ⊆ T'.val) := ⟨hTT'⟩
  have fST' : Fact (S ⊆ T'.val) := ⟨T'.property⟩
  let XT := curvePlaceSpaceLevelBaseChange k F T.property X
  have hXT : IsSeparated XT := hX.baseChange
  have hftT : FiniteTypeOverRing (curvePlaceSIntegers k F T.val) XT :=
    finiteTypeOverRing_baseChange _ hft
  have hlev := curve_transition (T := T'.val) XT (hS.mono T.property) hXT hftT
  let _ : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    curveAlgST k F
  let _ : Algebra (curvePlaceSIntegers k F T.val)
      (curvePlaceSIntegers k F T'.val) := curveAlgST k F
  let _ : Algebra (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T'.val) := curveAlgST k F
  have : IsScalarTower (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (curvePlaceSIntegers k F T'.val) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let e := towerIso (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
    (curvePlaceSIntegers k F T'.val) X
  have hiso := isHomeomorph_coordinate_iso (A := curvePlaceAdeleLevel k F T'.val)
    (CurvePlaceLevelFactor k F T'.val) (CurvePlaceLevelField k F T'.val)
    (curvePlaceLevelFieldAlgHom k F T'.val) (curvePlaceLevelFactorAlgHom k F T'.val) e
  have h₁ := curve_stageEquiv_isHomeomorph k F S (X := X) T
  have h₄ := curve_stageEquiv_isHomeomorph k F S (X := X) T'
  let _ : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs
      (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  have : IsScalarTower (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra (curvePlaceSIntegers k F T'.val) (curvePlaceAdeleLevelOver k F S T') :=
    inferInstanceAs
      (Algebra (curvePlaceSIntegers k F T'.val) (curvePlaceAdeleLevel k F T'.val))
  have : IsScalarTower (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T'.val) (curvePlaceAdeleLevelOver k F S T') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let _ : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T') :=
    curveAlgLevel k F
  have : IsScalarTower (curvePlaceSIntegers k F T.val)
      (curvePlaceSIntegers k F T'.val) (curvePlaceAdeleLevelOver k F S T') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T') :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hpt : ∀ p, curvePlaceSpaceStageEquiv k F S X T'
      (RingPoints.changeRing (curvePlaceAdeleLevelOverMap k F S h).hom p) =
      RingPoints.map e.hom (curvePlaceSpaceLevelTransition k F hTT' XT
        (curvePlaceSpaceStageEquiv k F S X T p)) := by
    intro p
    change (baseChangeRingPointsEquiv (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T'.val) (curvePlaceAdeleLevelOver k F S T') X).symm _ = _
    apply (Equiv.symm_apply_eq _).mpr
    change X.pullback _ p = X.pullback _ (X.pullback _ (X.pullback _ (X.pullback _ p)))
    refine (BaseChangeComparison.pullback_congr_left X (g := _ ≫ _ ≫ _ ≫ _) ?_ p).trans
      ((pullback_comp X _ _ _).trans (congrArg _ ((pullback_comp X _ _ _).trans
        (congrArg _ (pullback_comp X _ _ _)))))
    simp
    rfl
  let _ := curvePlaceSpaceStageTopology k F S X T
  let _ := curvePlaceSpaceStageTopology k F S X T'
  let _ := curvePlaceSpaceLevelTopology k F T.val XT
  let _ := curvePlaceSpaceLevelTopology k F T'.val (curvePlaceSpaceLevelBaseChange k F hTT' XT)
  let _ := curvePlaceSpaceLevelTopology k F T'.val (curvePlaceSpaceLevelBaseChange k F T'.property X)
  let _ := curvePlaceSpaceLevelTopology k F T'.val
    (baseChange (Spec.algebraMap (curvePlaceSIntegers k F T.val)
      (curvePlaceSIntegers k F T'.val))
      (baseChange (Spec.algebraMap (curvePlaceSIntegers k F S)
        (curvePlaceSIntegers k F T.val)) X))
  let _ := curvePlaceSpaceLevelTopology k F T'.val
    (baseChange (Spec.algebraMap (curvePlaceSIntegers k F S)
      (curvePlaceSIntegers k F T'.val)) X)
  have hfun : RingPoints.changeRing (curvePlaceAdeleLevelOverMap k F S h).hom =
      (curvePlaceSpaceStageEquiv k F S X T').symm ∘ (RingPoints.map e.hom ∘
        (curvePlaceSpaceLevelTransition k F hTT' XT ∘ curvePlaceSpaceStageEquiv k F S X T)) := by
    funext p
    exact ((Equiv.symm_apply_eq _).mpr (hpt p).symm).symm
  have h₄s : IsHomeomorph (curvePlaceSpaceStageEquiv k F S X T').symm :=
    (curvePlaceSpaceStageEquiv k F S X T').symm.isHomeomorph_iff.mpr
      ⟨(curvePlaceSpaceStageEquiv k F S X T').continuous_symm_iff.mpr h₄.isOpenMap, h₄.continuous⟩
  rw [hfun]
  exact h₄s.isOpenEmbedding.comp (hiso.isOpenEmbedding.comp (hlev.comp h₁.isOpenEmbedding))

/-- **Stages are open embeddings**, global function fields. -/
theorem curve_stage_isOpenEmbedding (hX : IsSeparated X) (hS : S.Nonempty)
    (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X) (T : AdelicLevelIndexAbove S) :
    @IsOpenEmbedding _ _ (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceAdelePointTopology k F S X) (curvePlaceSpaceStageMap k F S X T) :=
  Topology.FinalStage.isOpenEmbedding_stage (τ := curvePlaceSpaceStageTopology k F S X)
    (curvePlaceSpaceStageMap k F S X)
    (fun h => RingPoints.changeRing (curvePlaceAdeleLevelOverMap k F S h).hom)
    (fun h => curve_stage_transition k F S hX hS hft h)
    (fun h x => by
      simp only [curvePlaceSpaceStageMap, ProductPointsDescent.changeRing_changeRing]
      rfl)
    (fun T => RelativeIntegralPoints.changeRing_injective hX _ (curve_levelι_injective k F S T)) T

end Curve

end AdelicSpacePointStagesProof

end Langlands.Global
