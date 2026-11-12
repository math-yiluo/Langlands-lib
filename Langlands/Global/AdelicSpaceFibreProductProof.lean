import Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinateFibreProduct
import Langlands.Global.AdelicSpacePointsProof

/-!
# Fibre products of adelic points of separated algebraic spaces

Conrad, printed p.17: the topology on adelic points of separated algebraic spaces of finite type
over the `S`-integers is compatible with fibre products. For a pullback square
`P = X ×_Z Y`, the map `P(𝔸) → X(𝔸) × Y(𝔸)` is an embedding. This module proves this from one
input: every adelic point of `P` comes from a level.

* On each level the coordinate topology of `P` is induced from `X × Y`
  (`CoordinateFibreProduct`), and so on each stage.
* A point of `P(𝔸)` whose image lies in a stage of `X × Y` lies in the same stage of `P`,
  because the stage maps of the separated space `Z` are injective.
* The map is injective because `P` is a pullback.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointMaps
open Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinateFibreProduct
open Langlands.AlgebraicGeometry.PointTopology (ringTest)
open NumberField (RingOfIntegers)

namespace Langlands.Global

namespace AdelicSpaceFibreProductProof

open AdelicSpaceLocalFields AdelicSpacePointMapsProof AdelicSpacePointStagesProof

/-- Products of induced topologies are induced along the product map. -/
theorem prod_induced {α β γ δ : Type*} (f : α → γ) (g : β → δ) (tγ : TopologicalSpace γ)
    (tδ : TopologicalSpace δ) :
    @instTopologicalSpaceProd _ _ (TopologicalSpace.induced f tγ) (TopologicalSpace.induced g tδ) =
      TopologicalSpace.induced (Prod.map f g) (@instTopologicalSpaceProd _ _ tγ tδ) := by
  change TopologicalSpace.induced Prod.fst _ ⊓ TopologicalSpace.induced Prod.snd _ =
    TopologicalSpace.induced _ (TopologicalSpace.induced Prod.fst _ ⊓
      TopologicalSpace.induced Prod.snd _)
  rw [induced_inf, induced_compose, induced_compose, induced_compose, induced_compose]
  rfl

/-- A pullback square of presheaves is injective on sections. -/
theorem pullback_injective {S : Scheme.{u}} {P X Y Z : AlgebraicSpace S} {p₁ : P ⟶ X}
    {p₂ : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (T : Over S) : Function.Injective (fun w : P.sections T =>
      (mapSections p₁ T w, mapSections p₂ T w)) := fun _ _ hw =>
  ext_app_of_isPullback h T (congrArg Prod.fst hw) (congrArg Prod.snd hw)

section NumberField

variable (K : Type u) [Field K] [NumberField K]

section Level

variable (T : Finset (FinitePlace K))
  {P X Y Z : AlgebraicSpace (Spec (CommRingCat.of ((T : Set (FinitePlace K)).integer K)))}
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Every factor of a number-field level is compatible with fibre products. -/
theorem numberField_factor (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (hP : IsSeparated P) (hftP : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) P)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) Y)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) Z)
    (i : NumberFieldLevelFactorIndex K T) :
    fieldValuedPointTopology _ P (numberFieldLevelFieldAlgHom K T i) = TopologicalSpace.induced
      (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
      (@instTopologicalSpaceProd _ _ (fieldValuedPointTopology _ X (numberFieldLevelFieldAlgHom K T i))
        (fieldValuedPointTopology _ Y (numberFieldLevelFieldAlgHom K T i))) := by
  rcases i with v | v | v
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inl v)) := infiniteNormedField K v
    exact @fieldValued_eq_induced _ _ _ _ _ _ p₁ p₂ f g _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inl v)) h (infinite_isHenselianValuedField K v)
      hP hftP hX hftX hY hftY hZ hftZ _
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inl v))) :=
      normedField (RingOfIntegers K) K v.1
    exact @fieldValued_eq_induced _ _ _ _ _ _ p₁ p₂ f g _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inr (.inl v))) h
      (isHenselianValuedField (RingOfIntegers K) K v.1) hP hftP hX hftX hY hftY hZ hftZ _
  · let N : NontriviallyNormedField (NumberFieldLevelField K T (.inr (.inr v))) :=
      normedField (RingOfIntegers K) K v.1
    exact @fieldValued_eq_induced _ _ _ _ _ _ p₁ p₂ f g _ _ _ _ N
      (instAdelicSpaceLevelTopology6 K T (.inr (.inr v))) h
      (isHenselianValuedField (RingOfIntegers K) K v.1) hP hftP hX hftX hY hftY hZ hftZ _

/-- **Levels and fibre products**, number fields. -/
theorem numberField_level (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (hP : IsSeparated P) (hftP : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) P)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) Y)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing ((T : Set (FinitePlace K)).integer K) Z) :
    numberFieldSpaceLevelTopology K T P = TopologicalSpace.induced
      (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
      (@instTopologicalSpaceProd _ _ (numberFieldSpaceLevelTopology K T X)
        (numberFieldSpaceLevelTopology K T Y)) :=
  coordinate_eq_induced p₁ p₂ _ _ _ _
    (numberField_factor K T p₁ p₂ f g h hP hftP hX hftX hY hftY hZ hftZ)

end Level

variable (S : Finset (FinitePlace K))
  {P X Y Z : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)

/-- **Stages and fibre products**, number fields. -/
theorem numberField_stage (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (hP : IsSeparated P) (hftP : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) P)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Z)
    (T : AdelicLevelIndexAbove S) :
    numberFieldSpaceStageTopology K S P T = TopologicalSpace.induced
      (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
      (@instTopologicalSpaceProd _ _ (numberFieldSpaceStageTopology K S X T)
        (numberFieldSpaceStageTopology K S Y T)) := by
  have hT := numberField_level K T.val (numberFieldLevelMap K S T p₁)
    (numberFieldLevelMap K S T p₂) (numberFieldLevelMap K S T f) (numberFieldLevelMap K S T g)
    (isPullback_baseChange _ h) hP.baseChange (finiteTypeOverRing_baseChange _ hftP)
    hX.baseChange (finiteTypeOverRing_baseChange _ hftX) hY.baseChange
    (finiteTypeOverRing_baseChange _ hftY) hZ.baseChange (finiteTypeOverRing_baseChange _ hftZ)
  calc numberFieldSpaceStageTopology K S P T
      = TopologicalSpace.induced (numberFieldSpaceStageEquiv K S P T)
          (numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property P)) :=
        rfl
    _ = TopologicalSpace.induced (fun w => (numberFieldSpaceStageEquiv K S X T (RingPoints.map p₁ w),
          numberFieldSpaceStageEquiv K S Y T (RingPoints.map p₂ w)))
          (@instTopologicalSpaceProd _ _
            (numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X))
            (numberFieldSpaceLevelTopology K T.val
              (numberFieldSpaceLevelBaseChange K T.property Y))) := by
        rw [hT, induced_compose]
        congr 1
        funext w
        simp only [Function.comp_apply, numberField_stageEquiv_map]
    _ = TopologicalSpace.induced (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
          (TopologicalSpace.induced (Prod.map (numberFieldSpaceStageEquiv K S X T)
            (numberFieldSpaceStageEquiv K S Y T)) (@instTopologicalSpaceProd _ _
            (numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X))
            (numberFieldSpaceLevelTopology K T.val
              (numberFieldSpaceLevelBaseChange K T.property Y)))) := by
        rw [induced_compose]
        rfl
    _ = _ := by
        rw [← prod_induced]

/-- **Fibre products**, number fields: given that every adelic point of `P` comes from a level,
the map `P(𝔸) → X(𝔸) × Y(𝔸)` is an embedding. -/
theorem numberField_fibreProduct (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (hP : IsSeparated P) (hftP : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) P)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Z)
    (hcover : ∀ x : NumberFieldSpaceAdelePoints K S P, ∃ (T : AdelicLevelIndexAbove S)
      (y : RingPoints ((S : Set (FinitePlace K)).integer K) P (numberFieldAdeleLevelOver K S T)),
      numberFieldSpaceStageMap K S P T y = x) :
    letI := numberFieldSpaceAdelePointTopology K S X
    letI := numberFieldSpaceAdelePointTopology K S Y
    @IsEmbedding _ (NumberFieldSpaceAdelePoints K S X × NumberFieldSpaceAdelePoints K S Y)
      (numberFieldSpaceAdelePointTopology K S P) _
      (fun p => (RingPoints.map p₁ p, RingPoints.map p₂ p)) := by
  let _ := numberFieldSpaceAdelePointTopology K S P
  let _ := numberFieldSpaceAdelePointTopology K S X
  let _ := numberFieldSpaceAdelePointTopology K S Y
  let _ (T : AdelicLevelIndexAbove S) := numberFieldSpaceStageTopology K S P T
  let _ (T : AdelicLevelIndexAbove S) := numberFieldSpaceStageTopology K S X T
  let _ (T : AdelicLevelIndexAbove S) := numberFieldSpaceStageTopology K S Y T
  have hembP := numberField_stage_isOpenEmbedding K S hP hftP
  have hembX := numberField_stage_isOpenEmbedding K S hX hftX
  have hembY := numberField_stage_isOpenEmbedding K S hY hftY
  refine ⟨Topology.FinalStage.isInducing_of_stages (τ := numberFieldSpaceStageTopology K S P)
    (numberFieldSpaceStageMap K S P) hembP
    (fun T => Prod.map (numberFieldSpaceStageMap K S X T) (numberFieldSpaceStageMap K S Y T))
    (fun T => (hembX T).prodMap (hembY T)) _
    (fun _ w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
    (fun T => ⟨numberField_stage K S p₁ p₂ f g h hP hftP hX hftX hY hftY hZ hftZ T⟩)
    (fun T x => Prod.ext (RingPoints.changeRing_map _ _ _).symm
      (RingPoints.changeRing_map _ _ _).symm) (fun T z hz => ?_) hcover,
    pullback_injective h _⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := hz
  have hx : numberFieldSpaceStageMap K S X T x = RingPoints.map p₁ z := congrArg Prod.fst hxy
  have hy : numberFieldSpaceStageMap K S Y T y = RingPoints.map p₂ z := congrArg Prod.snd hxy
  have hw : ∀ w : NumberFieldSpaceAdelePoints K S P,
      RingPoints.map f (RingPoints.map p₁ w) = RingPoints.map g (RingPoints.map p₂ w) := fun w =>
    congrFun (congrArg (fun α => α.app (op (ringTest _ (numberFieldAdeleOver K S)))) h.w) w
  have hfg : RingPoints.map f x = RingPoints.map g y := by
    apply RelativeIntegralPoints.changeRing_injective hZ _ (numberField_levelι_injective K S T)
    change numberFieldSpaceStageMap K S Z T _ = numberFieldSpaceStageMap K S Z T _
    rw [numberFieldSpaceStageMap, RingPoints.changeRing_map, RingPoints.changeRing_map]
    change RingPoints.map f (numberFieldSpaceStageMap K S X T x) =
      RingPoints.map g (numberFieldSpaceStageMap K S Y T y)
    rw [hx, hy]
    exact hw z
  obtain ⟨w, hw₁, hw₂⟩ := exists_app_of_isPullback h _ x y hfg
  refine ⟨w, pullback_injective h _ ?_⟩
  refine Prod.ext ?_ ?_
  · exact (RingPoints.changeRing_map p₁ _ w).symm.trans
      ((congrArg (RingPoints.changeRing (numberFieldAdeleLevelOverι K S T).hom) hw₁).trans hx)
  · exact (RingPoints.changeRing_map p₂ _ w).symm.trans
      ((congrArg (RingPoints.changeRing (numberFieldAdeleLevelOverι K S T).hom) hw₂).trans hy)

end NumberField

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]

section Level

variable (T : Finset (AlgebraicCurve.Place k F))
  {P X Y Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F T)))}
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)

/-- Every factor of a curve-place level is compatible with fibre products. -/
theorem curve_factor (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (hP : IsSeparated P) (hftP : FiniteTypeOverRing (curvePlaceSIntegers k F T) P)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F T) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F T) Y)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing (curvePlaceSIntegers k F T) Z)
    (i : CurvePlaceLevelFactorIndex k F T) :
    fieldValuedPointTopology _ P (curvePlaceLevelFieldAlgHom k F T i) = TopologicalSpace.induced
      (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
      (@instTopologicalSpaceProd _ _ (fieldValuedPointTopology _ X (curvePlaceLevelFieldAlgHom k F T i))
        (fieldValuedPointTopology _ Y (curvePlaceLevelFieldAlgHom k F T i))) := by
  rcases i with v | v
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inl v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    exact @fieldValued_eq_induced _ _ _ _ _ _ p₁ p₂ f g _ _ _ _ N
      (instAdelicSpaceLevelTopology3 k F T (.inl v)) h
      (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum)
      hP hftP hX hftX hY hftY hZ hftZ _
  · let N : NontriviallyNormedField (CurvePlaceLevelField k F T (.inr v)) :=
      normedField v.1.toValuationSubring F v.1.heightOneSpectrum
    exact @fieldValued_eq_induced _ _ _ _ _ _ p₁ p₂ f g _ _ _ _ N
      (instAdelicSpaceLevelTopology3 k F T (.inr v)) h
      (isHenselianValuedField v.1.toValuationSubring F v.1.heightOneSpectrum)
      hP hftP hX hftX hY hftY hZ hftZ _

/-- **Levels and fibre products**, global function fields. -/
theorem curve_level (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (hP : IsSeparated P) (hftP : FiniteTypeOverRing (curvePlaceSIntegers k F T) P)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F T) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F T) Y)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing (curvePlaceSIntegers k F T) Z) :
    curvePlaceSpaceLevelTopology k F T P = TopologicalSpace.induced
      (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
      (@instTopologicalSpaceProd _ _ (curvePlaceSpaceLevelTopology k F T X)
        (curvePlaceSpaceLevelTopology k F T Y)) :=
  coordinate_eq_induced p₁ p₂ _ _ _ _
    (curve_factor k F T p₁ p₂ f g h hP hftP hX hftX hY hftY hZ hftZ)

end Level

variable (S : Finset (AlgebraicCurve.Place k F))
  {P X Y Z : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
  (p₁ : P ⟶ X) (p₂ : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)

/-- **Stages and fibre products**, global function fields. -/
theorem curve_stage (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (hP : IsSeparated P) (hftP : FiniteTypeOverRing (curvePlaceSIntegers k F S) P)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing (curvePlaceSIntegers k F S) Z)
    (T : AdelicLevelIndexAbove S) :
    curvePlaceSpaceStageTopology k F S P T = TopologicalSpace.induced
      (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
      (@instTopologicalSpaceProd _ _ (curvePlaceSpaceStageTopology k F S X T)
        (curvePlaceSpaceStageTopology k F S Y T)) := by
  have hT := curve_level k F T.val (curveLevelMap k F S T p₁)
    (curveLevelMap k F S T p₂) (curveLevelMap k F S T f) (curveLevelMap k F S T g)
    (isPullback_baseChange _ h) hP.baseChange (finiteTypeOverRing_baseChange _ hftP)
    hX.baseChange (finiteTypeOverRing_baseChange _ hftX) hY.baseChange
    (finiteTypeOverRing_baseChange _ hftY) hZ.baseChange (finiteTypeOverRing_baseChange _ hftZ)
  calc curvePlaceSpaceStageTopology k F S P T
      = TopologicalSpace.induced (curvePlaceSpaceStageEquiv k F S P T)
          (curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property P)) :=
        rfl
    _ = TopologicalSpace.induced (fun w => (curvePlaceSpaceStageEquiv k F S X T (RingPoints.map p₁ w),
          curvePlaceSpaceStageEquiv k F S Y T (RingPoints.map p₂ w)))
          (@instTopologicalSpaceProd _ _
            (curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X))
            (curvePlaceSpaceLevelTopology k F T.val
              (curvePlaceSpaceLevelBaseChange k F T.property Y))) := by
        rw [hT, induced_compose]
        congr 1
        funext w
        simp only [Function.comp_apply, curve_stageEquiv_map]
    _ = TopologicalSpace.induced (fun w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
          (TopologicalSpace.induced (Prod.map (curvePlaceSpaceStageEquiv k F S X T)
            (curvePlaceSpaceStageEquiv k F S Y T)) (@instTopologicalSpaceProd _ _
            (curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X))
            (curvePlaceSpaceLevelTopology k F T.val
              (curvePlaceSpaceLevelBaseChange k F T.property Y)))) := by
        rw [induced_compose]
        rfl
    _ = _ := by
        rw [← prod_induced]

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- **Fibre products**, global function fields: given that every adelic point of `P` comes from a level,
the map `P(𝔸) → X(𝔸) × Y(𝔸)` is an embedding. -/
theorem curve_fibreProduct (hS : S.Nonempty) (h : IsPullback (hom p₁) (hom p₂) (hom f) (hom g))
    (hP : IsSeparated P) (hftP : FiniteTypeOverRing (curvePlaceSIntegers k F S) P)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y)
    (hZ : IsSeparated Z) (hftZ : FiniteTypeOverRing (curvePlaceSIntegers k F S) Z)
    (hcover : ∀ x : CurvePlaceSpaceAdelePoints k F S P, ∃ (T : AdelicLevelIndexAbove S)
      (y : RingPoints (curvePlaceSIntegers k F S) P (curvePlaceAdeleLevelOver k F S T)),
      curvePlaceSpaceStageMap k F S P T y = x) :
    letI := curvePlaceSpaceAdelePointTopology k F S X
    letI := curvePlaceSpaceAdelePointTopology k F S Y
    @IsEmbedding _ (CurvePlaceSpaceAdelePoints k F S X × CurvePlaceSpaceAdelePoints k F S Y)
      (curvePlaceSpaceAdelePointTopology k F S P) _
      (fun p => (RingPoints.map p₁ p, RingPoints.map p₂ p)) := by
  let _ := curvePlaceSpaceAdelePointTopology k F S P
  let _ := curvePlaceSpaceAdelePointTopology k F S X
  let _ := curvePlaceSpaceAdelePointTopology k F S Y
  let _ (T : AdelicLevelIndexAbove S) := curvePlaceSpaceStageTopology k F S P T
  let _ (T : AdelicLevelIndexAbove S) := curvePlaceSpaceStageTopology k F S X T
  let _ (T : AdelicLevelIndexAbove S) := curvePlaceSpaceStageTopology k F S Y T
  have hembP := curve_stage_isOpenEmbedding k F S hP hS hftP
  have hembX := curve_stage_isOpenEmbedding k F S hX hS hftX
  have hembY := curve_stage_isOpenEmbedding k F S hY hS hftY
  refine ⟨Topology.FinalStage.isInducing_of_stages (τ := curvePlaceSpaceStageTopology k F S P)
    (curvePlaceSpaceStageMap k F S P) hembP
    (fun T => Prod.map (curvePlaceSpaceStageMap k F S X T) (curvePlaceSpaceStageMap k F S Y T))
    (fun T => (hembX T).prodMap (hembY T)) _
    (fun _ w => (RingPoints.map p₁ w, RingPoints.map p₂ w))
    (fun T => ⟨curve_stage k F S p₁ p₂ f g h hP hftP hX hftX hY hftY hZ hftZ T⟩)
    (fun T x => Prod.ext (RingPoints.changeRing_map _ _ _).symm
      (RingPoints.changeRing_map _ _ _).symm) (fun T z hz => ?_) hcover,
    pullback_injective h _⟩
  obtain ⟨⟨x, y⟩, hxy⟩ := hz
  have hx : curvePlaceSpaceStageMap k F S X T x = RingPoints.map p₁ z := congrArg Prod.fst hxy
  have hy : curvePlaceSpaceStageMap k F S Y T y = RingPoints.map p₂ z := congrArg Prod.snd hxy
  have hw : ∀ w : CurvePlaceSpaceAdelePoints k F S P,
      RingPoints.map f (RingPoints.map p₁ w) = RingPoints.map g (RingPoints.map p₂ w) := fun w =>
    congrFun (congrArg (fun α => α.app (op (ringTest _ (curvePlaceAdeleOver k F S)))) h.w) w
  have hfg : RingPoints.map f x = RingPoints.map g y := by
    apply RelativeIntegralPoints.changeRing_injective hZ _ (curve_levelι_injective k F S T)
    change curvePlaceSpaceStageMap k F S Z T _ = curvePlaceSpaceStageMap k F S Z T _
    rw [curvePlaceSpaceStageMap, RingPoints.changeRing_map, RingPoints.changeRing_map]
    change RingPoints.map f (curvePlaceSpaceStageMap k F S X T x) =
      RingPoints.map g (curvePlaceSpaceStageMap k F S Y T y)
    rw [hx, hy]
    exact hw z
  obtain ⟨w, hw₁, hw₂⟩ := exists_app_of_isPullback h _ x y hfg
  refine ⟨w, pullback_injective h _ ?_⟩
  refine Prod.ext ?_ ?_
  · exact (RingPoints.changeRing_map p₁ _ w).symm.trans
      ((congrArg (RingPoints.changeRing (curvePlaceAdeleLevelOverι k F S T).hom) hw₁).trans hx)
  · exact (RingPoints.changeRing_map p₂ _ w).symm.trans
      ((congrArg (RingPoints.changeRing (curvePlaceAdeleLevelOverι k F S T).hom) hw₂).trans hy)

end Curve

end AdelicSpaceFibreProductProof

end Langlands.Global
