import Langlands.Global.AdelicFixedModelClosedImmersionStatement
import Langlands.Global.AdelicLevelModelClosedImmersionProof

/-! # Closed embeddings for full-adele fixed-model points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- An injective coefficient map has a schematically dense spectrum map. -/
private theorem specMap_ker_eq_bot
    {A B : Type u} [CommRing A] [CommRing B]
    (a : A →+* B) (ha : Function.Injective a) :
    (Spec.map (CommRingCat.ofHom a)).ker = ⊥ := by
  have h : Function.Injective
      (((Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom a).hom) :=
    ha.comp (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
  rw [← Scheme.ΓSpecIso_naturality] at h
  change Function.Injective
    ((Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ∘
      (Spec.map (CommRingCat.ofHom a)).appTop.hom) at h
  have h' : Function.Injective (Spec.map (CommRingCat.ofHom a)).appTop.hom :=
    h.of_comp
  rw [Scheme.ker_of_isAffine, (RingHom.injective_iff_ker_eq_bot _).mp h']
  ext U
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Closed factorization descends along an injective coefficient map. -/
private theorem closedPointMap_lift
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) [IsClosedImmersion f.left]
    (a : A →ₐ[R] B) (ha : Function.Injective a)
    (y : RingPoint R Y A) (x : RingPoint R X B)
    (h : y.changeRing a = x ≫ f) :
    ∃ z : RingPoint R X A, z ≫ f = y ∧ z.changeRing a = x := by
  have hk : f.left.ker ≤ y.left.ker := by
    have hh := x.left.le_ker_comp f.left
    have he : Spec.map (CommRingCat.ofHom a.toRingHom) ≫ y.left =
        x.left ≫ f.left := congrArg (fun p : RingPoint R Y B => p.left) h
    rw [← he, Scheme.Hom.ker_comp, specMap_ker_eq_bot a.toRingHom ha,
      Scheme.IdealSheafData.map_bot] at hh
    exact hh
  let l := IsClosedImmersion.lift f.left y.left hk
  have hl : l ≫ f.left = y.left := IsClosedImmersion.lift_fac _ _ _
  let z : RingPoint R X A := Over.homMk l (by
    rw [← Over.w f, ← Category.assoc, hl]
    exact Over.w y)
  have hz : z ≫ f = y := by
    apply RingPoint.ext
    exact hl
  refine ⟨z, hz, ?_⟩
  apply RingPoint.ext
  apply (cancel_mono f.left).mp
  change (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ z.left) ≫ f.left =
    x.left ≫ f.left
  change (Spec.map (CommRingCat.ofHom a.toRingHom) ≫ l) ≫ f.left = _
  rw [Category.assoc, hl]
  exact congrArg (fun p : RingPoint R Y B => p.left) h

/-- Exact stagewise detection of images of sets under a closed immersion. -/
private theorem closedPointMap_preimage_image
    (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B]
    {X Y : Over (Spec (CommRingCat.of R))}
    (f : X ⟶ Y) [IsClosedImmersion f.left]
    (a : A →ₐ[R] B) (ha : Function.Injective a)
    (C : Set (RingPoint R X B)) :
    (fun p : RingPoint R Y A => p.changeRing a) ⁻¹'
        ((fun p : RingPoint R X B => p ≫ f) '' C) =
      (fun p : RingPoint R X A => p ≫ f) ''
        ((fun p : RingPoint R X A => p.changeRing a) ⁻¹' C) := by
  ext y
  constructor
  · rintro ⟨x, hx, hxy⟩
    obtain ⟨z, hz, hza⟩ := closedPointMap_lift R A B f a ha y x hxy.symm
    exact ⟨z, by simpa [hza] using hx, hz⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.changeRing a, hz, Category.assoc _ _ _⟩

/-- Closed stage maps and injective coefficient inclusions give a closed
embedding for the actual cocone point topologies. -/
private theorem closedPointMap_cocone_isClosedEmbedding
    (R : Type u) [CommRing R]
    {J : Type u} [SmallCategory J] (D : J ⥤ CommAlgCat.{u} R)
    (c : Cocone D) {X Y : Over (Spec (CommRingCat.of R))}
    (τX : ∀ j, TopologicalSpace (RingPoint R X (D.obj j)))
    (τY : ∀ j, TopologicalSpace (RingPoint R Y (D.obj j)))
    (f : X ⟶ Y) [IsClosedImmersion f.left]
    (hi : ∀ j, Function.Injective (c.ι.app j).hom)
    (hf : ∀ j, @IsClosedEmbedding
      (RingPoint R X (D.obj j)) (RingPoint R Y (D.obj j))
      (τX j) (τY j) (fun p => p ≫ f)) :
    @IsClosedEmbedding (RingPoint R X c.pt) (RingPoint R Y c.pt)
      (ringPointCoconeTopology R D X τX c)
      (ringPointCoconeTopology R D Y τY c) (fun p => p ≫ f) := by
  let := ringPointCoconeTopology R D X τX c
  let := ringPointCoconeTopology R D Y τY c
  apply IsClosedEmbedding.of_continuous_injective_isClosedMap
  · apply (ringPointCoconeTopology_continuous_iff R D X τX c _).2
    intro j
    let := τX j
    let := τY j
    exact ((ringPointCoconeTopology_continuous_ι R D Y τY c j).comp
      (hf j).continuous).congr (fun p => (Category.assoc _ _ _).symm)
  · intro p q h
    apply RingPoint.ext
    apply (cancel_mono f.left).mp
    exact congrArg (fun z : RingPoint R Y c.pt => z.left) h
  · intro C hC
    apply isOpen_compl_iff.mp
    apply (ringPointCoconeTopology_isOpen_iff R D Y τY c _).2
    intro j
    let := τX j
    let := τY j
    rw [Set.preimage_compl, closedPointMap_preimage_image R (D.obj j) c.pt f
      (c.ι.app j).hom (hi j)]
    exact ((hf j).isClosedMap _
      (hC.preimage (ringPointCoconeTopology_continuous_ι R D X τX c j))).isOpen_compl

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F] [FunctionField k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable {X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S)))}
variable (f : X ⟶ Y) [IsClosedImmersion f.left]
variable [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

/-- A closed immersion gives a closed embedding on each fixed-base stage. -/
theorem curvePlaceFixedModelStage_isClosedEmbedding (T : AdelicLevelIndexAbove S) :
    @IsClosedEmbedding
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
      (RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevelOver k F S T))
      (curvePlaceFixedModelStageTopology k F S X T)
      (curvePlaceFixedModelStageTopology k F S Y T) (fun p => p ≫ f) := by
  let := curvePlaceFixedModelStageTopology k F S X T
  let := curvePlaceFixedModelStageTopology k F S Y T
  let := curvePlaceLevelModelPointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property X)
  let := curvePlaceLevelModelPointTopology k F T.val
    (curvePlaceLevelModelBaseChange k F T.property Y)
  let eX := curvePlaceFixedModelPointHomeomorph k F S X T
  let eY := curvePlaceFixedModelPointHomeomorph k F S Y T
  let g := Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property))
  let fT : curvePlaceLevelModelBaseChange k F T.property X ⟶
      curvePlaceLevelModelBaseChange k F T.property Y := (Over.pullback g).map f
  let : IsClosedImmersion fT.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) g f inferInstance
  let : LocallyOfFiniteType (curvePlaceLevelModelBaseChange k F T.property Y).hom := by
    change LocallyOfFiniteType (pullback.snd Y.hom g)
    infer_instance
  let : QuasiCompact (curvePlaceLevelModelBaseChange k F T.property Y).hom := by
    change QuasiCompact (pullback.snd Y.hom g)
    infer_instance
  have hf := curvePlaceLevelModelPointMap_isClosedEmbedding k F T.val fT
  apply IsClosedEmbedding.of_comp eY.isEmbedding
  convert hf.comp eX.isClosedEmbedding using 1
  funext p
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ringPointBaseChangeEquiv_natural (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) f p

/-- Closed immersions are closed embeddings for actual full curve-place points. -/
theorem curvePlaceFixedModelAdele_isClosedEmbedding :
    @IsClosedEmbedding
      (CurvePlaceFixedModelAdelePoints k F S X)
      (CurvePlaceFixedModelAdelePoints k F S Y)
      (curvePlaceFixedModelAdelePointTopology k F S X)
      (curvePlaceFixedModelAdelePointTopology k F S Y) (fun p => p ≫ f) := by
  apply closedPointMap_cocone_isClosedEmbedding (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevelOverDiagram k F S) (curvePlaceAdeleOverCocone k F S)
    (curvePlaceFixedModelStageTopology k F S X)
    (curvePlaceFixedModelStageTopology k F S Y) f
  · intro T
    exact Subtype.val_injective
  · exact curvePlaceFixedModelStage_isClosedEmbedding k F S f

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K] (S : Finset (FinitePlace K))
variable {X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K)))}
variable (f : X ⟶ Y) [IsClosedImmersion f.left]
variable [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom]

/-- A closed immersion gives a closed embedding on each fixed-base stage. -/
theorem numberFieldFixedModelStage_isClosedEmbedding (T : AdelicLevelIndexAbove S) :
    @IsClosedEmbedding
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
      (RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevelOver K S T))
      (numberFieldFixedModelStageTopology K S X T)
      (numberFieldFixedModelStageTopology K S Y T) (fun p => p ≫ f) := by
  let := numberFieldFixedModelStageTopology K S X T
  let := numberFieldFixedModelStageTopology K S Y T
  let := numberFieldLevelModelPointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property X)
  let := numberFieldLevelModelPointTopology K T.val
    (numberFieldLevelModelBaseChange K T.property Y)
  let eX := numberFieldFixedModelPointHomeomorph K S X T
  let eY := numberFieldFixedModelPointHomeomorph K S Y T
  let g := Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property))
  let fT : numberFieldLevelModelBaseChange K T.property X ⟶
      numberFieldLevelModelBaseChange K T.property Y := (Over.pullback g).map f
  let : IsClosedImmersion fT.left :=
    MorphismProperty.overPullbackMap (P := @IsClosedImmersion) g f inferInstance
  let : LocallyOfFiniteType (numberFieldLevelModelBaseChange K T.property Y).hom := by
    change LocallyOfFiniteType (pullback.snd Y.hom g)
    infer_instance
  let : QuasiCompact (numberFieldLevelModelBaseChange K T.property Y).hom := by
    change QuasiCompact (pullback.snd Y.hom g)
    infer_instance
  have hf := numberFieldLevelModelPointMap_isClosedEmbedding K T.val fT
  apply IsClosedEmbedding.of_comp eY.isEmbedding
  convert hf.comp eX.isClosedEmbedding using 1
  funext p
  let : Algebra ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevel K T.val))
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ringPointBaseChangeEquiv_natural ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) f p

/-- Closed immersions are closed embeddings for actual full number-field points. -/
theorem numberFieldFixedModelAdele_isClosedEmbedding :
    @IsClosedEmbedding
      (NumberFieldFixedModelAdelePoints K S X) (NumberFieldFixedModelAdelePoints K S Y)
      (numberFieldFixedModelAdelePointTopology K S X)
      (numberFieldFixedModelAdelePointTopology K S Y) (fun p => p ≫ f) := by
  apply closedPointMap_cocone_isClosedEmbedding ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevelOverDiagram K S) (numberFieldAdeleOverCocone K S)
    (numberFieldFixedModelStageTopology K S X) (numberFieldFixedModelStageTopology K S Y) f
  · intro T
    exact Subtype.val_injective
  · exact numberFieldFixedModelStage_isClosedEmbedding K S f

end NumberField

/-- The exact full-adele fixed-model closed-immersion target in both cases. -/
theorem adelicFixedModelClosedImmersion : AdelicFixedModelClosedImmersionStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ S X Y f _ _ _
    exact curvePlaceFixedModelAdele_isClosedEmbedding k F S f
  · intro K _ _ S X Y f _ _ _
    exact numberFieldFixedModelAdele_isClosedEmbedding K S f

end Langlands.Global
