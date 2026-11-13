import Langlands.Global.AdelicSpaceSmoothConnectedModelOpen
import Langlands.Global.AdelicSpacePointTopologyTheorem
import Langlands.AlgebraicGeometry.AlgebraicSpace.TopologicalMorphismBaseChange

/-! # Cofinal passage from smooth connected levels to adelic points -/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps
open NumberField

namespace Langlands.Global

namespace AdelicSpaceOpenReduction

/-- Continuous source stages that cover suffice for the passage of openness,
even when only a cofinal selection of stages is used. -/
theorem isOpenMap_of_continuous_cover
    {I : Type*} {P Q : I → Type*} {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    (τP : ∀ i, TopologicalSpace (P i)) (τQ : ∀ i, TopologicalSpace (Q i))
    (sX : ∀ i, P i → X) (sY : ∀ i, Q i → Y) (f : X → Y) (fs : ∀ i, P i → Q i)
    (hcover : ∀ x, ∃ i, ∃ p, sX i p = x)
    (hsX : ∀ i, @Continuous _ _ (τP i) _ (sX i))
    (hfs : ∀ i, @IsOpenMap _ _ (τP i) (τQ i) (fs i))
    (hsY : ∀ i, @IsOpenMap _ _ (τQ i) _ (sY i))
    (hcomm : ∀ i p, f (sX i p) = sY i (fs i p)) :
    IsOpenMap f := by
  let : ∀ i, TopologicalSpace (P i) := τP
  let : ∀ i, TopologicalSpace (Q i) := τQ
  let s : (Σ i, P i) → X := fun p => sX p.1 p.2
  have hc : Continuous s := continuous_sigma hsX
  have hs : Function.Surjective s := by
    intro x
    obtain ⟨i, p, hp⟩ := hcover x
    exact ⟨⟨i, p⟩, hp⟩
  apply IsOpenMap.of_comp hc hs
  apply isOpenMap_sigma.mpr
  intro i
  change IsOpenMap (fun p => f (sX i p))
  have hn : (fun p => f (sX i p)) = sY i ∘ fs i := funext (hcomm i)
  rw [hn]
  exact (hsY i).comp (hfs i)

end AdelicSpaceOpenReduction

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))

/-- Regard the chosen principal level above T as a stage above the original S. -/
def curvePlaceSpacePrincipalStage (T : AdelicLevelIndexAbove S) : AdelicLevelIndexAbove S :=
  ⟨(curvePlacePrincipalLevelAbove k F T.val).val,
    T.property.trans (curvePlacePrincipalLevelAbove k F T.val).property⟩

variable {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- The exact estimate gives openness at a cofinal principal stage, without
requiring finite type over the integers for the original S-integer ring. -/
theorem curvePlaceSmoothConnectedPrincipalStage_isOpenMap
    (hLW : SpaceUniformLangWeilStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f)
    (T : AdelicLevelIndexAbove S) :
    @IsOpenMap _ _
      (curvePlaceSpaceStageTopology k F S X (curvePlaceSpacePrincipalStage k F S T))
      (curvePlaceSpaceStageTopology k F S Y (curvePlaceSpacePrincipalStage k F S T))
      (RingPoints.map f) := by
  let V := curvePlaceSpacePrincipalStage k F S T
  let : Algebra.FiniteType ℤ (curvePlaceSIntegers k F V.val) :=
    curvePlacePrincipalLevelAbove_finiteType k F T.val
  let := AdelicSpaceIntegerBase.algebra (curvePlaceSIntegers k F V.val)
  let := AdelicSpaceIntegerBase.locallyOfFiniteType (curvePlaceSIntegers k F V.val)
  let := curvePlaceSpaceStageTopology k F S X V
  let := curvePlaceSpaceStageTopology k F S Y V
  let := curvePlaceSpaceLevelTopology k F V.val (curvePlaceSpaceLevelBaseChange k F V.property X)
  let := curvePlaceSpaceLevelTopology k F V.val (curvePlaceSpaceLevelBaseChange k F V.property Y)
  let eX := curvePlaceSpaceStagePointHomeomorph k F S X V
  let eY := curvePlaceSpaceStagePointHomeomorph k F S Y V
  have hopen := curvePlaceSmoothConnectedLevel_isOpenMap k F V.val hLW (hS.mono V.property)
    hX.baseChange (finiteTypeOverRing_baseChange _ hXft)
    hY.baseChange (finiteTypeOverRing_baseChange _ hYft)
    (curvePlaceSpaceLevelModelMap k F S V f) hf.baseChangeMap hconn.baseChangeMap
  apply eY.comp_isOpenMap_iff.mp
  have hn : eY ∘ RingPoints.map (A := curvePlaceAdeleLevelOver k F S V) f =
      RingPoints.map (curvePlaceSpaceLevelModelMap k F S V f) ∘ eX :=
    funext (curvePlaceSpaceStageEquiv_map k F S V f)
  rw [hn]
  intro U hU
  rw [Set.image_comp]
  exact hopen _ (eX.isOpenMap U hU)

/-- Principal stages still cover the actual full adelic points. -/
theorem curvePlaceSpacePrincipalStage_cover (hS : S.Nonempty)
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (x : CurvePlaceSpaceAdelePoints k F S X) :
    ∃ (T : AdelicLevelIndexAbove S)
      (p : RingPoints (curvePlaceSIntegers k F S) X
        (curvePlaceAdeleLevelOver k F S (curvePlaceSpacePrincipalStage k F S T))),
      curvePlaceSpaceStageMap k F S X (curvePlaceSpacePrincipalStage k F S T) p = x := by
  obtain ⟨T, p, hp⟩ := (adelicSpacePointTopology.1.1 k F S hS X hX hXft).1 x
  have h : T ≤ curvePlaceSpacePrincipalStage k F S T :=
    (curvePlacePrincipalLevelAbove k F T.val).property
  exact ⟨T, RingPoints.changeRing (curvePlaceAdeleLevelOverMap k F S h).hom p,
    (AdelicSpacePointsProof.curve_stageMap_transition k F S h p).trans hp⟩

/-- A smooth map with nonempty geometrically connected fibres induces an open
map on actual model adelic points, conditional only on the exact space estimate. -/
theorem curvePlaceSmoothConnectedAdele_isOpenMap
    (hLW : SpaceUniformLangWeilStatement.{u}) (hS : S.Nonempty)
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    @IsOpenMap _ _ (curvePlaceSpaceAdelePointTopology k F S X)
      (curvePlaceSpaceAdelePointTopology k F S Y) (RingPoints.map f) := by
  let := curvePlaceSpaceAdelePointTopology k F S X
  let := curvePlaceSpaceAdelePointTopology k F S Y
  let (T : AdelicLevelIndexAbove S) :=
    curvePlaceSpaceStageTopology k F S X (curvePlaceSpacePrincipalStage k F S T)
  let (T : AdelicLevelIndexAbove S) :=
    curvePlaceSpaceStageTopology k F S Y (curvePlaceSpacePrincipalStage k F S T)
  exact AdelicSpaceOpenReduction.isOpenMap_of_continuous_cover
    (fun T => curvePlaceSpaceStageTopology k F S X (curvePlaceSpacePrincipalStage k F S T))
    (fun T => curvePlaceSpaceStageTopology k F S Y (curvePlaceSpacePrincipalStage k F S T))
    (fun T => curvePlaceSpaceStageMap k F S X (curvePlaceSpacePrincipalStage k F S T))
    (fun T => curvePlaceSpaceStageMap k F S Y (curvePlaceSpacePrincipalStage k F S T))
    (RingPoints.map f) (fun _ => RingPoints.map f)
    (curvePlaceSpacePrincipalStage_cover k F S hS hX hXft)
    (fun T => ((adelicSpacePointTopology.1.1 k F S hS X hX hXft).2.1
      (curvePlaceSpacePrincipalStage k F S T)).continuous)
    (curvePlaceSmoothConnectedPrincipalStage_isOpenMap k F S hLW hS hX hXft hY hYft f hf hconn)
    (fun T => ((adelicSpacePointTopology.1.1 k F S hS Y hY hYft).2.1
      (curvePlaceSpacePrincipalStage k F S T)).isOpenMap)
    (fun _ p => (RingPoints.changeRing_map f _ p).symm)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))

/-- Regard the chosen principal number-field level as a stage above the original S. -/
def numberFieldSpacePrincipalStage (T : AdelicLevelIndexAbove S) : AdelicLevelIndexAbove S :=
  ⟨(numberFieldPrincipalLevelAbove K T.val).val,
    T.property.trans (numberFieldPrincipalLevelAbove K T.val).property⟩

variable {X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- Openness at a cofinal principal stage retains every infinite factor. -/
theorem numberFieldSmoothConnectedPrincipalStage_isOpenMap
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f)
    (T : AdelicLevelIndexAbove S) :
    @IsOpenMap _ _
      (numberFieldSpaceStageTopology K S X (numberFieldSpacePrincipalStage K S T))
      (numberFieldSpaceStageTopology K S Y (numberFieldSpacePrincipalStage K S T))
      (RingPoints.map f) := by
  let V := numberFieldSpacePrincipalStage K S T
  let : Algebra.FiniteType ℤ ((V.val : Set (FinitePlace K)).integer K) :=
    numberFieldPrincipalLevelAbove_finiteType K T.val
  let := AdelicSpaceIntegerBase.algebra ((V.val : Set (FinitePlace K)).integer K)
  let := AdelicSpaceIntegerBase.locallyOfFiniteType ((V.val : Set (FinitePlace K)).integer K)
  let := numberFieldSpaceStageTopology K S X V
  let := numberFieldSpaceStageTopology K S Y V
  let := numberFieldSpaceLevelTopology K V.val (numberFieldSpaceLevelBaseChange K V.property X)
  let := numberFieldSpaceLevelTopology K V.val (numberFieldSpaceLevelBaseChange K V.property Y)
  let eX := numberFieldSpaceStagePointHomeomorph K S X V
  let eY := numberFieldSpaceStagePointHomeomorph K S Y V
  have hopen := numberFieldSmoothConnectedLevel_isOpenMap K V.val hLW
    hX.baseChange (finiteTypeOverRing_baseChange _ hXft)
    hY.baseChange (finiteTypeOverRing_baseChange _ hYft)
    (numberFieldSpaceLevelModelMap K S V f) hf.baseChangeMap hconn.baseChangeMap
  apply eY.comp_isOpenMap_iff.mp
  have hn : eY ∘ RingPoints.map (A := numberFieldAdeleLevelOver K S V) f =
      RingPoints.map (numberFieldSpaceLevelModelMap K S V f) ∘ eX :=
    funext (numberFieldSpaceStageEquiv_map K S V f)
  rw [hn]
  intro U hU
  rw [Set.image_comp]
  exact hopen _ (eX.isOpenMap U hU)

/-- Principal number-field stages cover the full adelic points, including
their infinite coordinates. -/
theorem numberFieldSpacePrincipalStage_cover
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (x : NumberFieldSpaceAdelePoints K S X) :
    ∃ (T : AdelicLevelIndexAbove S)
      (p : RingPoints ((S : Set (FinitePlace K)).integer K) X
        (numberFieldAdeleLevelOver K S (numberFieldSpacePrincipalStage K S T))),
      numberFieldSpaceStageMap K S X (numberFieldSpacePrincipalStage K S T) p = x := by
  obtain ⟨T, p, hp⟩ := (adelicSpacePointTopology.2.1 K S X hX hXft).1 x
  have h : T ≤ numberFieldSpacePrincipalStage K S T :=
    (numberFieldPrincipalLevelAbove K T.val).property
  exact ⟨T, RingPoints.changeRing (numberFieldAdeleLevelOverMap K S h).hom p,
    (AdelicSpacePointsProof.numberField_stageMap_transition K S h p).trans hp⟩

/-- The exact space estimate implies full number-field model adelic openness,
with no integer-base finite-type premise on the original ring. -/
theorem numberFieldSmoothConnectedAdele_isOpenMap
    (hLW : SpaceUniformLangWeilStatement.{u})
    (hX : IsSeparated X) (hXft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hYft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (f : X ⟶ Y) (hf : IsSmoothMorphism f) (hconn : HasGeometricallyConnectedFibres f) :
    @IsOpenMap _ _ (numberFieldSpaceAdelePointTopology K S X)
      (numberFieldSpaceAdelePointTopology K S Y) (RingPoints.map f) := by
  let := numberFieldSpaceAdelePointTopology K S X
  let := numberFieldSpaceAdelePointTopology K S Y
  let (T : AdelicLevelIndexAbove S) :=
    numberFieldSpaceStageTopology K S X (numberFieldSpacePrincipalStage K S T)
  let (T : AdelicLevelIndexAbove S) :=
    numberFieldSpaceStageTopology K S Y (numberFieldSpacePrincipalStage K S T)
  exact AdelicSpaceOpenReduction.isOpenMap_of_continuous_cover
    (fun T => numberFieldSpaceStageTopology K S X (numberFieldSpacePrincipalStage K S T))
    (fun T => numberFieldSpaceStageTopology K S Y (numberFieldSpacePrincipalStage K S T))
    (fun T => numberFieldSpaceStageMap K S X (numberFieldSpacePrincipalStage K S T))
    (fun T => numberFieldSpaceStageMap K S Y (numberFieldSpacePrincipalStage K S T))
    (RingPoints.map f) (fun _ => RingPoints.map f)
    (numberFieldSpacePrincipalStage_cover K S hX hXft)
    (fun T => ((adelicSpacePointTopology.2.1 K S X hX hXft).2.1
      (numberFieldSpacePrincipalStage K S T)).continuous)
    (numberFieldSmoothConnectedPrincipalStage_isOpenMap K S hLW hX hXft hY hYft f hf hconn)
    (fun T => ((adelicSpacePointTopology.2.1 K S Y hY hYft).2.1
      (numberFieldSpacePrincipalStage K S T)).isOpenMap)
    (fun _ p => (RingPoints.changeRing_map f _ p).symm)

end NumberField

end Langlands.Global
