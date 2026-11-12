import Langlands.AlgebraicGeometry.AlgebraicSpace.CoordinatePointOpenMap
import Langlands.Global.AdelicSpacePointTopology

/-! # Coordinate and stage reductions for adelic openness of algebraic spaces -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry (AlgebraicSpace)
open Langlands.AlgebraicGeometry.AlgebraicSpace

namespace Langlands.Global

namespace AdelicSpaceOpenReduction

/-- Open maps on stages induce an open map on the final point spaces when the source
stages cover and the target stage maps are open. -/
theorem isOpenMap_of_stages {I : Type*} {P Q : I → Type*} {X Y : Type*}
    (τP : ∀ i, TopologicalSpace (P i)) (τQ : ∀ i, TopologicalSpace (Q i))
    (sX : ∀ i, P i → X) (sY : ∀ i, Q i → Y) (f : X → Y) (fs : ∀ i, P i → Q i)
    (hcover : ∀ x, ∃ i, ∃ p, sX i p = x)
    (hfs : ∀ i, @IsOpenMap _ _ (τP i) (τQ i) (fs i))
    (hsY : ∀ i, @IsOpenMap _ _ (τQ i)
      (⨆ j, TopologicalSpace.coinduced (sY j) (τQ j)) (sY i))
    (hcomm : ∀ i p, f (sX i p) = sY i (fs i p)) :
    @IsOpenMap _ _ (⨆ i, TopologicalSpace.coinduced (sX i) (τP i))
      (⨆ i, TopologicalSpace.coinduced (sY i) (τQ i)) f := by
  let : ∀ i, TopologicalSpace (P i) := τP
  let : ∀ i, TopologicalSpace (Q i) := τQ
  let : TopologicalSpace X := ⨆ i, TopologicalSpace.coinduced (sX i) (τP i)
  let : TopologicalSpace Y := ⨆ i, TopologicalSpace.coinduced (sY i) (τQ i)
  let s : (Σ i, P i) → X := fun p => sX p.1 p.2
  have hc : Continuous s :=
    continuous_sigma fun i => continuous_iSup_rng continuous_coinduced_rng
  have hs : Function.Surjective s := by
    intro x
    obtain ⟨i, p, hp⟩ := hcover x
    exact ⟨⟨i, p⟩, hp⟩
  apply IsOpenMap.of_comp hc hs
  apply isOpenMap_sigma.mpr
  intro i
  have hn : (fun p => f (sX i p)) = sY i ∘ fs i := funext (hcomm i)
  change IsOpenMap (fun p => f (sX i p))
  rw [hn]
  exact (hsY i).comp (hfs i)

end AdelicSpaceOpenReduction

section Curve

variable (k F : Type u) [Field k] [Finite k] [Field F] [Algebra k F]
  [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
  (S : Finset (AlgebraicCurve.Place k F))

/-- The actual adelic-level coordinate bijection as a homeomorphism. -/
def curvePlaceSpaceLevelPointHomeomorph
    (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (hS : S.Nonempty) (hX : IsSeparated X) (hft : FiniteTypeOverRing (curvePlaceSIntegers k F S) X) :
    @Homeomorph (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevel k F S))
      (∀ i, RingPoints (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F S i))
      (curvePlaceSpaceLevelTopology k F S X)
      (coordinateProductTopology (curvePlaceSIntegers k F S) X (CurvePlaceLevelFactor k F S)
        (CurvePlaceLevelField k F S) (curvePlaceLevelFieldAlgHom k F S)) :=
  coordinatePointHomeomorph (CurvePlaceLevelFactor k F S) (CurvePlaceLevelField k F S)
    (curvePlaceLevelFieldAlgHom k F S) (curvePlaceLevelFactorAlgHom k F S) X
    (curvePlaceSpaceLevelPoints k F S hS X hX hft)

variable {X Y : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}

/-- Local openness and cofinite component surjectivity give openness at a level. -/
theorem curvePlaceSpaceLevel_isOpenMap_of_local (hS : S.Nonempty)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y) (f : X ⟶ Y)
    (ho : ∀ i, @IsOpenMap _ _ (fieldValuedPointTopology (curvePlaceSIntegers k F S) X (curvePlaceLevelFieldAlgHom k F S i))
      (fieldValuedPointTopology (curvePlaceSIntegers k F S) Y (curvePlaceLevelFieldAlgHom k F S i)) (RingPoints.map f))
    (hs : ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := CurvePlaceLevelFactor k F S i) f)) :
    @IsOpenMap _ _ (curvePlaceSpaceLevelTopology k F S X)
      (curvePlaceSpaceLevelTopology k F S Y) (RingPoints.map f) :=
  isOpenMap_coordinatePointMap_of_local (CurvePlaceLevelFactor k F S) (CurvePlaceLevelField k F S)
    (curvePlaceLevelFieldAlgHom k F S) (curvePlaceLevelFactorAlgHom k F S) f
    (curvePlaceSpaceLevelPoints k F S hS X hX hftX) (curvePlaceSpaceLevelPoints k F S hS Y hY hftY) ho hs

/-- Base change of a model morphism to an enlarged integer ring. -/
def curvePlaceSpaceLevelModelMap (T : AdelicLevelIndexAbove S) (f : X ⟶ Y) :
    curvePlaceSpaceLevelBaseChange k F T.property X ⟶ curvePlaceSpaceLevelBaseChange k F T.property Y :=
  baseChangeMap _ f

/-- The stage identification, with its defining induced topology, as a homeomorphism. -/
def curvePlaceSpaceStagePointHomeomorph
    (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))) (T : AdelicLevelIndexAbove S) :
    @Homeomorph
      (RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
      (RingPoints (curvePlaceSIntegers k F T.val) (curvePlaceSpaceLevelBaseChange k F T.property X) (curvePlaceAdeleLevel k F T.val))
      (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X)) :=
  letI := curvePlaceSpaceStageTopology k F S X T
  letI := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X)
  (curvePlaceSpaceStageEquiv k F S X T).toHomeomorphOfIsInducing ⟨rfl⟩

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- Naturality of the stage identification in a morphism of models. -/
theorem curvePlaceSpaceStageEquiv_map (T : AdelicLevelIndexAbove S) (f : X ⟶ Y)
    (p : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :
    curvePlaceSpaceStageEquiv k F S Y T (RingPoints.map f p) =
      RingPoints.map (curvePlaceSpaceLevelModelMap k F S T f) (curvePlaceSpaceStageEquiv k F S X T p) := by
  let _ : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let _ : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  have : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change (baseChangeRingPointsEquiv (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) Y).symm (RingPoints.map f p) =
    RingPoints.map (baseChangeMap (Spec.algebraMap (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)) f)
      ((baseChangeRingPointsEquiv (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
        (curvePlaceAdeleLevelOver k F S T) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_map, Equiv.apply_symm_apply]

/-- Local openness and cofinite component surjectivity give openness on an actual stage. -/
theorem curvePlaceSpaceStage_isOpenMap_of_local (hS : S.Nonempty)
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing (curvePlaceSIntegers k F S) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing (curvePlaceSIntegers k F S) Y) (f : X ⟶ Y)
    (T : AdelicLevelIndexAbove S)
    (ho : ∀ i, @IsOpenMap _ _ (fieldValuedPointTopology (curvePlaceSIntegers k F T.val)
        (curvePlaceSpaceLevelBaseChange k F T.property X) (curvePlaceLevelFieldAlgHom k F T.val i))
      (fieldValuedPointTopology (curvePlaceSIntegers k F T.val)
        (curvePlaceSpaceLevelBaseChange k F T.property Y) (curvePlaceLevelFieldAlgHom k F T.val i)) (RingPoints.map (curvePlaceSpaceLevelModelMap k F S T f)))
    (hs : ∀ᶠ i in Filter.cofinite, Function.Surjective
      (RingPoints.map (A := CurvePlaceLevelFactor k F T.val i) (curvePlaceSpaceLevelModelMap k F S T f))) :
    @IsOpenMap _ _ (curvePlaceSpaceStageTopology k F S X T)
      (curvePlaceSpaceStageTopology k F S Y T) (RingPoints.map f) := by
  let := curvePlaceSpaceStageTopology k F S X T
  let := curvePlaceSpaceStageTopology k F S Y T
  let := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property X)
  let := curvePlaceSpaceLevelTopology k F T.val (curvePlaceSpaceLevelBaseChange k F T.property Y)
  let eX := curvePlaceSpaceStagePointHomeomorph k F S X T
  let eY := curvePlaceSpaceStagePointHomeomorph k F S Y T
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have hopen := curvePlaceSpaceLevel_isOpenMap_of_local k F T.val (Finset.Nonempty.mono T.property hS)
    hX.baseChange hftX.baseChange hY.baseChange hftY.baseChange (curvePlaceSpaceLevelModelMap k F S T f) ho hs
  apply eY.comp_isOpenMap_iff.mp
  have hn : eY ∘ RingPoints.map (A := curvePlaceAdeleLevelOver k F S T) f =
      RingPoints.map (curvePlaceSpaceLevelModelMap k F S T f) ∘ eX :=
    funext (curvePlaceSpaceStageEquiv_map k F S T f)
  rw [hn]
  intro U hU
  rw [Set.image_comp]
  exact hopen _ (eX.isOpenMap U hU)

omit [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F] in
/-- The remaining topological passage to full adelic points. Coverage of source stages and
openness of target stage inclusions are explicit inputs. -/
theorem curvePlaceSpaceAdele_isOpenMap_of_stages (f : X ⟶ Y)
    (hcover : ∀ x : CurvePlaceSpaceAdelePoints k F S X,
      ∃ (T : AdelicLevelIndexAbove S)
        (p : RingPoints (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)),
        curvePlaceSpaceStageMap k F S X T p = x)
    (hstage : ∀ T : AdelicLevelIndexAbove S,
      @IsOpenMap _ _ (curvePlaceSpaceStageTopology k F S X T) (curvePlaceSpaceStageTopology k F S Y T) (RingPoints.map f))
    (htarget : ∀ T : AdelicLevelIndexAbove S,
      @IsOpenMap _ _ (curvePlaceSpaceStageTopology k F S Y T)
        (curvePlaceSpaceAdelePointTopology k F S Y) (curvePlaceSpaceStageMap k F S Y T)) :
    @IsOpenMap _ _ (curvePlaceSpaceAdelePointTopology k F S X)
      (curvePlaceSpaceAdelePointTopology k F S Y) (RingPoints.map f) :=
  AdelicSpaceOpenReduction.isOpenMap_of_stages
    (curvePlaceSpaceStageTopology k F S X) (curvePlaceSpaceStageTopology k F S Y)
    (curvePlaceSpaceStageMap k F S X) (curvePlaceSpaceStageMap k F S Y)
    (RingPoints.map f) (fun _ => RingPoints.map f) hcover hstage htarget
    (fun _ p => (RingPoints.changeRing_map f _ p).symm)



/-- The identification with generic-fibre adelic points is natural in a morphism of models. -/
theorem curvePlaceSpaceGenericFiberEquiv_map (f : X ⟶ Y)
    (p : CurvePlaceSpaceAdelePoints k F S X) :
    curvePlaceSpaceGenericFiberEquiv k F S Y (RingPoints.map f p) =
      RingPoints.map (baseChangeMap (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) f)
        (curvePlaceSpaceGenericFiberEquiv k F S X p) := by
  let algSF : Algebra (curvePlaceSIntegers k F S) F := (curvePlaceSIntegers k F S).subtype.toAlgebra
  let algSA : Algebra (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S) :=
    (curvePlaceAdeleOver k F S).algebra
  let algFA : Algebra F (curvePlaceAdeleOver k F S) :=
    inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF algFA algSA (curvePlaceAdeleLevelDiagonal_eq k F S)
  change (baseChangeRingPointsEquiv (curvePlaceSIntegers k F S) F
      (curvePlaceAdeleOver k F S) Y).symm (RingPoints.map f p) =
    RingPoints.map (baseChangeMap (Spec.algebraMap (curvePlaceSIntegers k F S) F) f)
      ((baseChangeRingPointsEquiv (curvePlaceSIntegers k F S) F
        (curvePlaceAdeleOver k F S) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_map, Equiv.apply_symm_apply]

/-- A morphism square between generic fibres gives a commuting square on adelic points. -/
theorem curvePlaceSpaceSpreadEquiv_map_of_model
    (W V : AlgebraicSpace (Spec (CommRingCat.of F)))
    (e : curvePlaceSpaceGenericFiber k F S X ≅ W)
    (d : curvePlaceSpaceGenericFiber k F S Y ≅ V)
    (f : X ⟶ Y) (g : W ⟶ V)
    (hmodel : baseChangeMap (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) f ≫ d.hom = e.hom ≫ g)
    (p : CurvePlaceSpaceAdelePoints k F S X) :
    curvePlaceSpaceSpreadEquiv k F S Y V d (RingPoints.map f p) =
      RingPoints.map g (curvePlaceSpaceSpreadEquiv k F S X W e p) := by
  change RingPoints.map d.hom (curvePlaceSpaceGenericFiberEquiv k F S Y (RingPoints.map f p)) =
    RingPoints.map g (RingPoints.map e.hom (curvePlaceSpaceGenericFiberEquiv k F S X p))
  rw [curvePlaceSpaceGenericFiberEquiv_map k F S f]
  change RingPoints.map (baseChangeMap (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) f ≫ d.hom)
      (curvePlaceSpaceGenericFiberEquiv k F S X p) =
    RingPoints.map (e.hom ≫ g) (curvePlaceSpaceGenericFiberEquiv k F S X p)
  rw [hmodel]
  rfl

/-- Transport from model adelic points to a specified generic fibre, with the defining
spread topology. -/
def curvePlaceSpaceSpreadPointHomeomorph
    (X : AlgebraicSpace (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
    (W : AlgebraicSpace (Spec (CommRingCat.of F)))
    (e : curvePlaceSpaceGenericFiber k F S X ≅ W) :
    @Homeomorph (CurvePlaceSpaceAdelePoints k F S X) (CurvePlaceSpaceFieldAdelePoints k F W)
      (curvePlaceSpaceAdelePointTopology k F S X)
      (curvePlaceSpaceSpreadTopology k F S X W e) :=
  letI := curvePlaceSpaceAdelePointTopology k F S X
  letI := curvePlaceSpaceSpreadTopology k F S X W e
  ((curvePlaceSpaceSpreadEquiv k F S X W e).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

/-- A compatible open model point map is open after transport to specified generic fibres.
The commutativity condition is a square of morphisms on the actual generic fibres. -/
theorem curvePlaceSpaceSpread_isOpenMap_of_model
    (W V : AlgebraicSpace (Spec (CommRingCat.of F)))
    (e : curvePlaceSpaceGenericFiber k F S X ≅ W)
    (d : curvePlaceSpaceGenericFiber k F S Y ≅ V)
    (f : X ⟶ Y) (g : W ⟶ V)
    (hf : @IsOpenMap _ _ (curvePlaceSpaceAdelePointTopology k F S X)
      (curvePlaceSpaceAdelePointTopology k F S Y) (RingPoints.map f))
    (hmodel : baseChangeMap (Spec.map (CommRingCat.ofHom (curvePlaceSIntegers k F S).subtype)) f ≫ d.hom = e.hom ≫ g) :
    @IsOpenMap _ _ (curvePlaceSpaceSpreadTopology k F S X W e)
      (curvePlaceSpaceSpreadTopology k F S Y V d) (RingPoints.map g) := by
  let := curvePlaceSpaceAdelePointTopology k F S X
  let := curvePlaceSpaceAdelePointTopology k F S Y
  let := curvePlaceSpaceSpreadTopology k F S X W e
  let := curvePlaceSpaceSpreadTopology k F S Y V d
  let eX := curvePlaceSpaceSpreadPointHomeomorph k F S X W e
  let eY := curvePlaceSpaceSpreadPointHomeomorph k F S Y V d
  have hn : RingPoints.map g = eY ∘ RingPoints.map f ∘ eX.symm := by
    funext p
    change RingPoints.map g p = eY (RingPoints.map f (eX.symm p))
    rw [show eY (RingPoints.map f (eX.symm p)) =
      RingPoints.map g (eX (eX.symm p)) from curvePlaceSpaceSpreadEquiv_map_of_model k F S W V e d f g hmodel
        (eX.symm p), eX.apply_symm_apply]
  rw [hn]
  exact eY.isOpenMap.comp (hf.comp eX.symm.isOpenMap)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
  (S : Finset (FinitePlace K))

/-- The actual adelic-level coordinate bijection as a homeomorphism. -/
def numberFieldSpaceLevelPointHomeomorph
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (hX : IsSeparated X) (hft : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X) :
    @Homeomorph (RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevel K S))
      (∀ i, RingPoints ((S : Set (FinitePlace K)).integer K) X (NumberFieldLevelFactor K S i))
      (numberFieldSpaceLevelTopology K S X)
      (coordinateProductTopology ((S : Set (FinitePlace K)).integer K) X (NumberFieldLevelFactor K S)
        (NumberFieldLevelField K S) (numberFieldLevelFieldAlgHom K S)) :=
  coordinatePointHomeomorph (NumberFieldLevelFactor K S) (NumberFieldLevelField K S)
    (numberFieldLevelFieldAlgHom K S) (numberFieldLevelFactorAlgHom K S) X
    (numberFieldSpaceLevelPoints K S X hX hft)

variable {X Y : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}

/-- Local openness and cofinite component surjectivity give openness at a level. -/
theorem numberFieldSpaceLevel_isOpenMap_of_local
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y)
    (ho : ∀ i, @IsOpenMap _ _ (fieldValuedPointTopology ((S : Set (FinitePlace K)).integer K) X (numberFieldLevelFieldAlgHom K S i))
      (fieldValuedPointTopology ((S : Set (FinitePlace K)).integer K) Y (numberFieldLevelFieldAlgHom K S i)) (RingPoints.map f))
    (hs : ∀ᶠ i in Filter.cofinite,
      Function.Surjective (RingPoints.map (A := NumberFieldLevelFactor K S i) f)) :
    @IsOpenMap _ _ (numberFieldSpaceLevelTopology K S X)
      (numberFieldSpaceLevelTopology K S Y) (RingPoints.map f) :=
  isOpenMap_coordinatePointMap_of_local (NumberFieldLevelFactor K S) (NumberFieldLevelField K S)
    (numberFieldLevelFieldAlgHom K S) (numberFieldLevelFactorAlgHom K S) f
    (numberFieldSpaceLevelPoints K S X hX hftX) (numberFieldSpaceLevelPoints K S Y hY hftY) ho hs

/-- Base change of a model morphism to an enlarged integer ring. -/
def numberFieldSpaceLevelModelMap (T : AdelicLevelIndexAbove S) (f : X ⟶ Y) :
    numberFieldSpaceLevelBaseChange K T.property X ⟶ numberFieldSpaceLevelBaseChange K T.property Y :=
  baseChangeMap _ f

/-- The stage identification, with its defining induced topology, as a homeomorphism. -/
def numberFieldSpaceStagePointHomeomorph
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))) (T : AdelicLevelIndexAbove S) :
    @Homeomorph
      (RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
      (RingPoints ((T.val : Set (FinitePlace K)).integer K) (numberFieldSpaceLevelBaseChange K T.property X) (numberFieldAdeleLevel K T.val))
      (numberFieldSpaceStageTopology K S X T)
      (numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X)) :=
  letI := numberFieldSpaceStageTopology K S X T
  letI := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X)
  (numberFieldSpaceStageEquiv K S X T).toHomeomorphOfIsInducing ⟨rfl⟩

/-- Naturality of the stage identification in a morphism of models. -/
theorem numberFieldSpaceStageEquiv_map (T : AdelicLevelIndexAbove S) (f : X ⟶ Y)
    (p : RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :
    numberFieldSpaceStageEquiv K S Y T (RingPoints.map f p) =
      RingPoints.map (numberFieldSpaceLevelModelMap K S T f) (numberFieldSpaceStageEquiv K S X T p) := by
  let _ : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let _ : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  have : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  change (baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) Y).symm (RingPoints.map f p) =
    RingPoints.map (baseChangeMap (Spec.algebraMap ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)) f)
      ((baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
        (numberFieldAdeleLevelOver K S T) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_map, Equiv.apply_symm_apply]

/-- Local openness and cofinite component surjectivity give openness on an actual stage. -/
theorem numberFieldSpaceStage_isOpenMap_of_local
    (hX : IsSeparated X) (hftX : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) X)
    (hY : IsSeparated Y) (hftY : FiniteTypeOverRing ((S : Set (FinitePlace K)).integer K) Y) (f : X ⟶ Y)
    (T : AdelicLevelIndexAbove S)
    (ho : ∀ i, @IsOpenMap _ _ (fieldValuedPointTopology ((T.val : Set (FinitePlace K)).integer K)
        (numberFieldSpaceLevelBaseChange K T.property X) (numberFieldLevelFieldAlgHom K T.val i))
      (fieldValuedPointTopology ((T.val : Set (FinitePlace K)).integer K)
        (numberFieldSpaceLevelBaseChange K T.property Y) (numberFieldLevelFieldAlgHom K T.val i)) (RingPoints.map (numberFieldSpaceLevelModelMap K S T f)))
    (hs : ∀ᶠ i in Filter.cofinite, Function.Surjective
      (RingPoints.map (A := NumberFieldLevelFactor K T.val i) (numberFieldSpaceLevelModelMap K S T f))) :
    @IsOpenMap _ _ (numberFieldSpaceStageTopology K S X T)
      (numberFieldSpaceStageTopology K S Y T) (RingPoints.map f) := by
  let := numberFieldSpaceStageTopology K S X T
  let := numberFieldSpaceStageTopology K S Y T
  let := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property X)
  let := numberFieldSpaceLevelTopology K T.val (numberFieldSpaceLevelBaseChange K T.property Y)
  let eX := numberFieldSpaceStagePointHomeomorph K S X T
  let eY := numberFieldSpaceStagePointHomeomorph K S Y T
  have : MorphismProperty.IsStableUnderBaseChange
      (@LocallyOfFiniteType.{u} ⊓ @QuasiCompact.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.inf
  have hopen := numberFieldSpaceLevel_isOpenMap_of_local K T.val
    hX.baseChange hftX.baseChange hY.baseChange hftY.baseChange (numberFieldSpaceLevelModelMap K S T f) ho hs
  apply eY.comp_isOpenMap_iff.mp
  have hn : eY ∘ RingPoints.map (A := numberFieldAdeleLevelOver K S T) f =
      RingPoints.map (numberFieldSpaceLevelModelMap K S T f) ∘ eX :=
    funext (numberFieldSpaceStageEquiv_map K S T f)
  rw [hn]
  intro U hU
  rw [Set.image_comp]
  exact hopen _ (eX.isOpenMap U hU)

/-- The remaining topological passage to full adelic points. Coverage of source stages and
openness of target stage inclusions are explicit inputs. -/
theorem numberFieldSpaceAdele_isOpenMap_of_stages (f : X ⟶ Y)
    (hcover : ∀ x : NumberFieldSpaceAdelePoints K S X,
      ∃ (T : AdelicLevelIndexAbove S)
        (p : RingPoints ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)),
        numberFieldSpaceStageMap K S X T p = x)
    (hstage : ∀ T : AdelicLevelIndexAbove S,
      @IsOpenMap _ _ (numberFieldSpaceStageTopology K S X T) (numberFieldSpaceStageTopology K S Y T) (RingPoints.map f))
    (htarget : ∀ T : AdelicLevelIndexAbove S,
      @IsOpenMap _ _ (numberFieldSpaceStageTopology K S Y T)
        (numberFieldSpaceAdelePointTopology K S Y) (numberFieldSpaceStageMap K S Y T)) :
    @IsOpenMap _ _ (numberFieldSpaceAdelePointTopology K S X)
      (numberFieldSpaceAdelePointTopology K S Y) (RingPoints.map f) :=
  AdelicSpaceOpenReduction.isOpenMap_of_stages
    (numberFieldSpaceStageTopology K S X) (numberFieldSpaceStageTopology K S Y)
    (numberFieldSpaceStageMap K S X) (numberFieldSpaceStageMap K S Y)
    (RingPoints.map f) (fun _ => RingPoints.map f) hcover hstage htarget
    (fun _ p => (RingPoints.changeRing_map f _ p).symm)



/-- The identification with generic-fibre adelic points is natural in a morphism of models. -/
theorem numberFieldSpaceGenericFiberEquiv_map (f : X ⟶ Y)
    (p : NumberFieldSpaceAdelePoints K S X) :
    numberFieldSpaceGenericFiberEquiv K S Y (RingPoints.map f p) =
      RingPoints.map (baseChangeMap (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) f)
        (numberFieldSpaceGenericFiberEquiv K S X p) := by
  let algSF : Algebra ((S : Set (FinitePlace K)).integer K) K := ((S : Set (FinitePlace K)).integer K).toSubring.subtype.toAlgebra
  let algSA : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K S).algebra
  let algFA : Algebra K (numberFieldAdeleOver K S) :=
    inferInstanceAs (Algebra K (Adeles K))
  let tower := @IsScalarTower.of_algebraMap_eq _ _ _ _ _ _ algSF algFA algSA (fun _ => rfl)
  change (baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K) K
      (numberFieldAdeleOver K S) Y).symm (RingPoints.map f p) =
    RingPoints.map (baseChangeMap (Spec.algebraMap ((S : Set (FinitePlace K)).integer K) K) f)
      ((baseChangeRingPointsEquiv ((S : Set (FinitePlace K)).integer K) K
        (numberFieldAdeleOver K S) X).symm p)
  rw [Equiv.symm_apply_eq, baseChangeRingPointsEquiv_map, Equiv.apply_symm_apply]

/-- A morphism square between generic fibres gives a commuting square on adelic points. -/
theorem numberFieldSpaceSpreadEquiv_map_of_model
    (W V : AlgebraicSpace (Spec (CommRingCat.of K)))
    (e : numberFieldSpaceGenericFiber K S X ≅ W)
    (d : numberFieldSpaceGenericFiber K S Y ≅ V)
    (f : X ⟶ Y) (g : W ⟶ V)
    (hmodel : baseChangeMap (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) f ≫ d.hom = e.hom ≫ g)
    (p : NumberFieldSpaceAdelePoints K S X) :
    numberFieldSpaceSpreadEquiv K S Y V d (RingPoints.map f p) =
      RingPoints.map g (numberFieldSpaceSpreadEquiv K S X W e p) := by
  change RingPoints.map d.hom (numberFieldSpaceGenericFiberEquiv K S Y (RingPoints.map f p)) =
    RingPoints.map g (RingPoints.map e.hom (numberFieldSpaceGenericFiberEquiv K S X p))
  rw [numberFieldSpaceGenericFiberEquiv_map K S f]
  change RingPoints.map (baseChangeMap (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) f ≫ d.hom)
      (numberFieldSpaceGenericFiberEquiv K S X p) =
    RingPoints.map (e.hom ≫ g) (numberFieldSpaceGenericFiberEquiv K S X p)
  rw [hmodel]
  rfl

/-- Transport from model adelic points to a specified generic fibre, with the defining
spread topology. -/
def numberFieldSpaceSpreadPointHomeomorph
    (X : AlgebraicSpace (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
    (W : AlgebraicSpace (Spec (CommRingCat.of K)))
    (e : numberFieldSpaceGenericFiber K S X ≅ W) :
    @Homeomorph (NumberFieldSpaceAdelePoints K S X) (NumberFieldSpaceFieldAdelePoints K W)
      (numberFieldSpaceAdelePointTopology K S X)
      (numberFieldSpaceSpreadTopology K S X W e) :=
  letI := numberFieldSpaceAdelePointTopology K S X
  letI := numberFieldSpaceSpreadTopology K S X W e
  ((numberFieldSpaceSpreadEquiv K S X W e).symm.toHomeomorphOfIsInducing ⟨rfl⟩).symm

/-- A compatible open model point map is open after transport to specified generic fibres.
The commutativity condition is a square of morphisms on the actual generic fibres. -/
theorem numberFieldSpaceSpread_isOpenMap_of_model
    (W V : AlgebraicSpace (Spec (CommRingCat.of K)))
    (e : numberFieldSpaceGenericFiber K S X ≅ W)
    (d : numberFieldSpaceGenericFiber K S Y ≅ V)
    (f : X ⟶ Y) (g : W ⟶ V)
    (hf : @IsOpenMap _ _ (numberFieldSpaceAdelePointTopology K S X)
      (numberFieldSpaceAdelePointTopology K S Y) (RingPoints.map f))
    (hmodel : baseChangeMap (Spec.map (CommRingCat.ofHom ((S : Set (FinitePlace K)).integer K).toSubring.subtype)) f ≫ d.hom = e.hom ≫ g) :
    @IsOpenMap _ _ (numberFieldSpaceSpreadTopology K S X W e)
      (numberFieldSpaceSpreadTopology K S Y V d) (RingPoints.map g) := by
  let := numberFieldSpaceAdelePointTopology K S X
  let := numberFieldSpaceAdelePointTopology K S Y
  let := numberFieldSpaceSpreadTopology K S X W e
  let := numberFieldSpaceSpreadTopology K S Y V d
  let eX := numberFieldSpaceSpreadPointHomeomorph K S X W e
  let eY := numberFieldSpaceSpreadPointHomeomorph K S Y V d
  have hn : RingPoints.map g = eY ∘ RingPoints.map f ∘ eX.symm := by
    funext p
    change RingPoints.map g p = eY (RingPoints.map f (eX.symm p))
    rw [show eY (RingPoints.map f (eX.symm p)) =
      RingPoints.map g (eX (eX.symm p)) from numberFieldSpaceSpreadEquiv_map_of_model K S W V e d f g hmodel
        (eX.symm p), eX.apply_symm_apply]
  rw [hn]
  exact eY.isOpenMap.comp (hf.comp eX.symm.isOpenMap)

end NumberField

end Langlands.Global
