import Langlands.Global.AdelicFixedModelProperMapStatement
import Langlands.Global.AdelicFixedModelFunctorialityProof
import Langlands.Global.AdelicFixedModelFiniteTypeProof
import Langlands.Global.AdelicFullLevelPreimageProof
import Langlands.Global.AdelicLevelModelProperMapProof

/-! # Properness of full-adele fixed-model maps -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology

/-- A final target topology and exact stage preimages detect properness. -/
private theorem isProperMap_of_final_stages
    {I A B : Type u} [TopologicalSpace A] [TopologicalSpace B]
    (As Bs : I → Type u) [∀ i, TopologicalSpace (As i)] [∀ i, TopologicalSpace (Bs i)]
    (f : A → B) (a : ∀ i, As i → A) (b : ∀ i, Bs i → B)
    (g : ∀ i, As i → Bs i)
    (hf : Continuous f) (ha : ∀ i, Continuous (a i))
    (hb : ∀ i, Function.Injective (b i))
    (hcomm : ∀ i x, f (a i x) = b i (g i x))
    (hpre : ∀ i, f ⁻¹' Set.range (b i) = Set.range (a i))
    (hfinal : ∀ C : Set B, IsClosed C ↔ ∀ i, IsClosed (b i ⁻¹' C))
    (hcover : ∀ y, ∃ i z, b i z = y)
    (hg : ∀ i, IsProperMap (g i)) : IsProperMap f := by
  rw [isProperMap_iff_isClosedMap_and_compact_fibers]
  refine ⟨hf, ?_, ?_⟩
  · intro C hC
    apply (hfinal _).2
    intro i
    have heq : b i ⁻¹' (f '' C) = g i '' (a i ⁻¹' C) := by
      ext y
      constructor
      · rintro ⟨x, hx, hxy⟩
        have hxstage : x ∈ Set.range (a i) := by
          rw [← hpre i]
          exact ⟨y, hxy.symm⟩
        obtain ⟨z, rfl⟩ := hxstage
        exact ⟨z, hx, hb i ((hcomm i z).symm.trans hxy)⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨a i x, hx, hcomm i x⟩
    rw [heq]
    exact (hg i).isClosedMap _ (hC.preimage (ha i))
  · intro y
    obtain ⟨i, z, rfl⟩ := hcover y
    have heq : f ⁻¹' {b i z} = a i '' (g i ⁻¹' {z}) := by
      ext x
      constructor
      · intro hx
        have hxy : f x = b i z := hx
        have hxstage : x ∈ Set.range (a i) := by
          rw [← hpre i]
          exact ⟨z, hxy.symm⟩
        obtain ⟨w, rfl⟩ := hxstage
        exact ⟨w, hb i ((hcomm i w).symm.trans hxy), rfl⟩
      · rintro ⟨w, hw, rfl⟩
        change f (a i w) = b i z
        exact (hcomm i w).trans (congrArg (b i) hw)
    rw [heq]
    exact ((hg i).isCompact_preimage isCompact_singleton).image (ha i)

/-- The final point topology can equally be tested on closed preimages. -/
private theorem ringPointCoconeTopology_isClosed_iff
    (R : Type u) [CommRing R] {J : Type u} [SmallCategory J]
    (D : J ⥤ CommAlgCat.{u} R) (X : Over (Spec (CommRingCat.of R)))
    (τ : ∀ j, TopologicalSpace (RingPoint R X (D.obj j))) (c : Cocone D)
    (C : Set (RingPoint R X c.pt)) :
    @IsClosed _ (ringPointCoconeTopology R D X τ c) C ↔
      ∀ j, @IsClosed _ (τ j)
        ((fun p : RingPoint R X (D.obj j) => p.changeRing (c.ι.app j).hom) ⁻¹' C) := by
  simpa only [← isOpen_compl_iff, Set.preimage_compl] using
    ringPointCoconeTopology_isOpen_iff R D X τ c Cᶜ

/-- Forgetting base change commutes with compatible coefficient maps. -/
private theorem ringPointBaseChangeEquiv_symm_changeRing
    (C D A B : Type u) [CommRing C] [CommRing D] [CommRing A] [CommRing B]
    [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
    [Algebra C B] [Algebra D B] [IsScalarTower C D B]
    (aC : A →ₐ[C] B) (aD : A →ₐ[D] B) (ha : aC.toRingHom = aD.toRingHom)
    (X : Over (Spec (CommRingCat.of C)))
    (p : RingPoint D (ringBaseChange C D X) A) :
    (ringPointBaseChangeEquiv C D B X).symm (RingPoint.changeRing aD p) =
      RingPoint.changeRing aC ((ringPointBaseChangeEquiv C D A X).symm p) := by
  apply RingPoint.ext
  rw [ringPointBaseChangeEquiv_symm_left]
  change (Spec.map (CommRingCat.ofHom aD.toRingHom) ≫ p.left) ≫ _ =
    Spec.map (CommRingCat.ofHom aC.toRingHom) ≫
      ((ringPointBaseChangeEquiv C D A X).symm p).left
  rw [ringPointBaseChangeEquiv_symm_left, ha]
  exact Category.assoc _ _ _

/-- The base-change point comparison is natural in compatible coefficient maps. -/
private theorem ringPointBaseChangeEquiv_changeRing
    (C D A B : Type u) [CommRing C] [CommRing D] [CommRing A] [CommRing B]
    [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
    [Algebra C B] [Algebra D B] [IsScalarTower C D B]
    (aC : A →ₐ[C] B) (aD : A →ₐ[D] B) (ha : aC.toRingHom = aD.toRingHom)
    (X : Over (Spec (CommRingCat.of C))) (p : RingPoint C X A) :
    ringPointBaseChangeEquiv C D B X (RingPoint.changeRing aC p) =
      RingPoint.changeRing aD (ringPointBaseChangeEquiv C D A X p) := by
  apply (ringPointBaseChangeEquiv C D B X).symm.injective
  rw [Equiv.symm_apply_apply, ringPointBaseChangeEquiv_symm_changeRing C D A B aC aD ha,
    Equiv.symm_apply_apply]

/-- Exact coefficient-range preimages descend along a change of model base. -/
private theorem ringPointBaseChange_preimage
    (C D A B : Type u) [CommRing C] [CommRing D] [CommRing A] [CommRing B]
    [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
    [Algebra C B] [Algebra D B] [IsScalarTower C D B]
    (aC : A →ₐ[C] B) (aD : A →ₐ[D] B) (ha : aC.toRingHom = aD.toRingHom)
    (X Y : Over (Spec (CommRingCat.of C))) (f : X ⟶ Y)
    (h : (fun p : RingPoint D (ringBaseChange C D X) B =>
      p ≫ (Over.pullback (Spec.algebraMap C D)).map f) ⁻¹'
        Set.range (RingPoint.changeRing (X := ringBaseChange C D Y) aD) =
      Set.range (RingPoint.changeRing (X := ringBaseChange C D X) aD)) :
    (fun p : RingPoint C X B => p ≫ f) ⁻¹'
        Set.range (RingPoint.changeRing (X := Y) aC) =
      Set.range (RingPoint.changeRing (X := X) aC) := by
  ext p
  constructor
  · rintro ⟨q, hq⟩
    have hp : ringPointBaseChangeEquiv C D B X p ∈
        Set.range (RingPoint.changeRing (X := ringBaseChange C D X) aD) := by
      rw [← h]
      refine ⟨ringPointBaseChangeEquiv C D A Y q, ?_⟩
      rw [← ringPointBaseChangeEquiv_changeRing C D A B aC aD ha,
        hq, ringPointBaseChangeEquiv_natural]
    obtain ⟨r, hr⟩ := hp
    refine ⟨(ringPointBaseChangeEquiv C D A X).symm r, ?_⟩
    rw [← ringPointBaseChangeEquiv_symm_changeRing C D A B aC aD ha,
      hr, Equiv.symm_apply_apply]
  · rintro ⟨q, rfl⟩
    exact ⟨q ≫ f, (Category.assoc _ _ _).symm⟩

section Curve

variable (k F : Type u) [Field k] [Field F] [Algebra k F]
variable (S : Finset (AlgebraicCurve.Place k F))
variable (X Y : Over (Spec (CommRingCat.of (curvePlaceSIntegers k F S))))
variable [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) [IsProper f.left]

/-- Properness gives exact preimages at every enlarged fixed-base level. -/
private theorem curvePlaceFixedModel_stage_preimage (T : AdelicLevelIndexAbove S) :
    (fun p : CurvePlaceFixedModelAdelePoints k F S X => p ≫ f) ⁻¹'
        Set.range (RingPoint.changeRing (X := Y) (curvePlaceAdeleLevelOverι k F S T).hom) =
      Set.range (RingPoint.changeRing (X := X) (curvePlaceAdeleLevelOverι k F S T).hom) := by
  let : Algebra (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) :=
    (curvePlaceSIntegersMap k F T.property).toAlgebra
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T) :=
    inferInstanceAs (Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevel k F T.val))
  let : Algebra (curvePlaceSIntegers k F T.val) (curvePlaceAdeleOver k F S) :=
    (curvePlaceAdeleOver k F T.val).algebra
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleLevelOver k F S T) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)
      (curvePlaceAdeleOver k F S) := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let aD : curvePlaceAdeleLevelOver k F S T →ₐ[curvePlaceSIntegers k F T.val]
      curvePlaceAdeleOver k F S :=
    { toRingHom := (curvePlaceAdeleLevel k F T.val).subtype, commutes' := fun _ => rfl }
  let XT := ringBaseChange (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) X
  let YT := ringBaseChange (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val) Y
  let fT : XT ⟶ YT := (Over.pullback (Spec.algebraMap
    (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val))).map f
  let : QuasiCompact YT.hom := by
    change QuasiCompact (pullback.snd Y.hom _)
    infer_instance
  let : IsSeparated YT.hom := by
    change IsSeparated (pullback.snd Y.hom _)
    infer_instance
  let : IsProper fT.left := MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.algebraMap (curvePlaceSIntegers k F S) (curvePlaceSIntegers k F T.val)) f
      inferInstance
  exact ringPointBaseChange_preimage (curvePlaceSIntegers k F S)
    (curvePlaceSIntegers k F T.val) (curvePlaceAdeleLevelOver k F S T)
    (curvePlaceAdeleOver k F S) (curvePlaceAdeleLevelOverι k F S T).hom aD rfl X Y f
      (adelicFullLevelPreimage.1 k F T.val XT YT fT)

omit [QuasiCompact Y.hom] in
/-- The literal level inclusion is injective on separated model points. -/
private theorem curvePlaceFixedModel_stage_injective (T : AdelicLevelIndexAbove S) :
    Function.Injective
      (RingPoint.changeRing (X := Y) (curvePlaceAdeleLevelOverι k F S T).hom) := by
  let : ∀ i, IsReduced (CurvePlaceLevelFactor k F T.val i) := fun i => by
    cases i with
    | inl v => exact inferInstanceAs (IsReduced (curvePlaceCompletion v.1))
    | inr v => exact inferInstanceAs (IsReduced (curvePlaceCompletionIntegers v.1))
  let : IsReduced (curvePlaceAdeleLevelOver k F S T) :=
    isReduced_of_injective (curvePlaceLevelFactorRingEquiv k F T.val)
      (curvePlaceLevelFactorRingEquiv k F T.val).injective
  exact schemeSeparatedCoefficientInjectivity_proof (curvePlaceSIntegers k F S)
    (curvePlaceAdeleLevelOver k F S T) (curvePlaceAdeleOver k F S) Y
    (curvePlaceAdeleLevelOverι k F S T).hom Subtype.val_injective

variable [Finite k] [Algebra (RatFunc k) F] [IsScalarTower k (RatFunc k) F]
variable [FunctionField k F] [LocallyOfFiniteType Y.hom]

/-- Properness on an enlarged model transfers to its original fixed-base points. -/
private theorem curvePlaceFixedModel_stage_proper (T : AdelicLevelIndexAbove S) :
    letI := curvePlaceFixedModelStageTopology k F S X T
    letI := curvePlaceFixedModelStageTopology k F S Y T
    IsProperMap
      (X := RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
      (Y := RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevelOver k F S T))
      (fun p : RingPoint (curvePlaceSIntegers k F S) X
      (curvePlaceAdeleLevelOver k F S T) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y
          (curvePlaceAdeleLevelOver k F S T))) := by
  let := curvePlaceFixedModelStageTopology k F S X T
  let := curvePlaceFixedModelStageTopology k F S Y T
  let XT := curvePlaceLevelModelBaseChange k F T.property X
  let YT := curvePlaceLevelModelBaseChange k F T.property Y
  let fT : XT ⟶ YT := (Over.pullback
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property)))).map f
  let : LocallyOfFiniteType YT.hom := by
    change LocallyOfFiniteType (pullback.snd Y.hom _)
    infer_instance
  let : QuasiCompact YT.hom := by
    change QuasiCompact (pullback.snd Y.hom _)
    infer_instance
  let : IsSeparated YT.hom := by
    change IsSeparated (pullback.snd Y.hom _)
    infer_instance
  let : IsProper fT.left := MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.map (CommRingCat.ofHom (curvePlaceSIntegersMap k F T.property))) f inferInstance
  let := curvePlaceLevelModelPointTopology k F T.val XT
  let := curvePlaceLevelModelPointTopology k F T.val YT
  let eX := curvePlaceFixedModelPointHomeomorph k F S X T
  let eY := curvePlaceFixedModelPointHomeomorph k F S Y T
  have hf := adelicLevelModelProperMap.1 k F T.val XT YT fT
  have heq : (eY.symm ∘ (fun p => p ≫ fT) ∘ eX) =
      (fun p : RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T) =>
        (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevelOver k F S T))) := by
    funext p
    change (curvePlaceFixedModelPointEquiv k F S Y T).symm
      (curvePlaceFixedModelPointEquiv k F S X T p ≫ _) = p ≫ f
    exact (congrArg (curvePlaceFixedModelPointEquiv k F S Y T).symm
      (curvePlaceFixedModelPointEquiv_natural k F S f T p)).symm.trans
        ((curvePlaceFixedModelPointEquiv k F S Y T).symm_apply_apply (p ≫ f))
  rw [← heq]
  exact eY.symm.isProperMap.comp (hf.comp eX.isProperMap)

/-- The full-adele map of a proper function-field model morphism is proper. -/
theorem curvePlaceFixedModel_proper :
    letI := curvePlaceFixedModelAdelePointTopology k F S X
    letI := curvePlaceFixedModelAdelePointTopology k F S Y
    IsProperMap
      (X := CurvePlaceFixedModelAdelePoints k F S X)
      (Y := CurvePlaceFixedModelAdelePoints k F S Y)
      (fun p : CurvePlaceFixedModelAdelePoints k F S X =>
        (p ≫ f : CurvePlaceFixedModelAdelePoints k F S Y)) := by
  let := curvePlaceFixedModelAdelePointTopology k F S X
  let := curvePlaceFixedModelAdelePointTopology k F S Y
  let : ∀ T, TopologicalSpace
      (RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T)) :=
    curvePlaceFixedModelStageTopology k F S X
  let : ∀ T, TopologicalSpace
      (RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevelOver k F S T)) :=
    curvePlaceFixedModelStageTopology k F S Y
  exact isProperMap_of_final_stages
    (A := CurvePlaceFixedModelAdelePoints k F S X)
    (B := CurvePlaceFixedModelAdelePoints k F S Y)
    (fun T => RingPoint (curvePlaceSIntegers k F S) X (curvePlaceAdeleLevelOver k F S T))
    (fun T => RingPoint (curvePlaceSIntegers k F S) Y (curvePlaceAdeleLevelOver k F S T))
    (fun p => p ≫ f)
    (fun T => RingPoint.changeRing (X := X) (curvePlaceAdeleLevelOverι k F S T).hom)
    (fun T => RingPoint.changeRing (X := Y) (curvePlaceAdeleLevelOverι k F S T).hom)
    (fun T p => (p ≫ f : RingPoint (curvePlaceSIntegers k F S) Y
      (curvePlaceAdeleLevelOver k F S T)))
    (curvePlaceFixedModelAdele_continuous k F S f)
    (ringPointCoconeTopology_continuous_ι (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevelOverDiagram k F S) X (curvePlaceFixedModelStageTopology k F S X)
      (curvePlaceAdeleOverCocone k F S))
    (curvePlaceFixedModel_stage_injective k F S Y)
    (fun _ _ => Category.assoc _ _ _)
    (curvePlaceFixedModel_stage_preimage k F S X Y f)
    (ringPointCoconeTopology_isClosed_iff (curvePlaceSIntegers k F S)
      (curvePlaceAdeleLevelOverDiagram k F S) Y (curvePlaceFixedModelStageTopology k F S Y)
      (curvePlaceAdeleOverCocone k F S))
    (adelicFixedModelFiniteType.1 k F S Y).1
    (curvePlaceFixedModel_stage_proper k F S X Y f)

end Curve

section NumberField

variable (K : Type u) [Field K] [NumberField K]
variable (S : Finset (FinitePlace K))
variable (X Y : Over (Spec (CommRingCat.of ((S : Set (FinitePlace K)).integer K))))
variable [QuasiCompact Y.hom] [IsSeparated Y.hom] (f : X ⟶ Y) [IsProper f.left]

/-- Properness gives exact preimages at every enlarged full number-field level. -/
private theorem numberFieldFixedModel_stage_preimage (T : AdelicLevelIndexAbove S) :
    (fun p : NumberFieldFixedModelAdelePoints K S X => p ≫ f) ⁻¹'
        Set.range (RingPoint.changeRing (X := Y) (numberFieldAdeleLevelOverι K S T).hom) =
      Set.range (RingPoint.changeRing (X := X) (numberFieldAdeleLevelOverι K S T).hom) := by
  let : Algebra ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) :=
    (numberFieldSIntegersMap K T.property).toAlgebra
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    inferInstanceAs (Algebra ((T.val : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevel K T.val))
  let : Algebra ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    (numberFieldAdeleOver K T.val).algebra
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let : IsScalarTower ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let aD : numberFieldAdeleLevelOver K S T →ₐ[((T.val : Set (FinitePlace K)).integer K)]
      numberFieldAdeleOver K S :=
    { toRingHom := (numberFieldAdeleLevel K T.val).subtype, commutes' := fun _ => rfl }
  let XT := ringBaseChange ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) X
  let YT := ringBaseChange ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) Y
  let fT : XT ⟶ YT := (Over.pullback (Spec.algebraMap
    ((S : Set (FinitePlace K)).integer K) ((T.val : Set (FinitePlace K)).integer K))).map f
  let : QuasiCompact YT.hom := by
    change QuasiCompact (pullback.snd Y.hom _)
    infer_instance
  let : IsSeparated YT.hom := by
    change IsSeparated (pullback.snd Y.hom _)
    infer_instance
  let : IsProper fT.left := MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.algebraMap ((S : Set (FinitePlace K)).integer K)
      ((T.val : Set (FinitePlace K)).integer K)) f inferInstance
  exact ringPointBaseChange_preimage ((S : Set (FinitePlace K)).integer K)
    ((T.val : Set (FinitePlace K)).integer K) (numberFieldAdeleLevelOver K S T)
    (numberFieldAdeleOver K S) (numberFieldAdeleLevelOverι K S T).hom aD rfl X Y f
      (adelicFullLevelPreimage.2 K T.val XT YT fT)

omit [QuasiCompact Y.hom] in
/-- The full number-field level inclusion is injective on separated points. -/
private theorem numberFieldFixedModel_stage_injective (T : AdelicLevelIndexAbove S) :
    Function.Injective
      (RingPoint.changeRing (X := Y) (numberFieldAdeleLevelOverι K S T).hom) := by
  let : ∀ i, IsReduced (NumberFieldLevelFactor K T.val i) := fun i => by
    cases i with
    | inl v => exact inferInstanceAs (IsReduced (InfiniteCompletion K v))
    | inr i =>
      cases i with
      | inl v => exact inferInstanceAs (IsReduced (FiniteCompletion K v.1))
      | inr v => exact inferInstanceAs (IsReduced (v.1.adicCompletionIntegers K))
  let : IsReduced (numberFieldAdeleLevelOver K S T) :=
    isReduced_of_injective (numberFieldLevelFactorRingEquiv K T.val)
      (numberFieldLevelFactorRingEquiv K T.val).injective
  exact schemeSeparatedCoefficientInjectivity_proof ((S : Set (FinitePlace K)).integer K)
    (numberFieldAdeleLevelOver K S T) (numberFieldAdeleOver K S) Y
    (numberFieldAdeleLevelOverι K S T).hom Subtype.val_injective

variable [LocallyOfFiniteType Y.hom]

/-- Full number-field level properness transfers to original fixed-base points. -/
private theorem numberFieldFixedModel_stage_proper (T : AdelicLevelIndexAbove S) :
    letI := numberFieldFixedModelStageTopology K S X T
    letI := numberFieldFixedModelStageTopology K S Y T
    IsProperMap
      (X := RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
      (Y := RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevelOver K S T))
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X
      (numberFieldAdeleLevelOver K S T) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (numberFieldAdeleLevelOver K S T))) := by
  let := numberFieldFixedModelStageTopology K S X T
  let := numberFieldFixedModelStageTopology K S Y T
  let XT := numberFieldLevelModelBaseChange K T.property X
  let YT := numberFieldLevelModelBaseChange K T.property Y
  let fT : XT ⟶ YT := (Over.pullback
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property)))).map f
  let : LocallyOfFiniteType YT.hom := by
    change LocallyOfFiniteType (pullback.snd Y.hom _)
    infer_instance
  let : QuasiCompact YT.hom := by
    change QuasiCompact (pullback.snd Y.hom _)
    infer_instance
  let : IsSeparated YT.hom := by
    change IsSeparated (pullback.snd Y.hom _)
    infer_instance
  let : IsProper fT.left := MorphismProperty.overPullbackMap (P := @IsProper)
    (Spec.map (CommRingCat.ofHom (numberFieldSIntegersMap K T.property))) f inferInstance
  let := numberFieldLevelModelPointTopology K T.val XT
  let := numberFieldLevelModelPointTopology K T.val YT
  let eX := numberFieldFixedModelPointHomeomorph K S X T
  let eY := numberFieldFixedModelPointHomeomorph K S Y T
  have hf := adelicLevelModelProperMap.2 K T.val XT YT fT
  have heq : (eY.symm ∘ (fun p => p ≫ fT) ∘ eX) =
      (fun p : RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T) =>
        (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
          (numberFieldAdeleLevelOver K S T))) := by
    funext p
    change (numberFieldFixedModelPointEquiv K S Y T).symm
      (numberFieldFixedModelPointEquiv K S X T p ≫ _) = p ≫ f
    exact (congrArg (numberFieldFixedModelPointEquiv K S Y T).symm
      (numberFieldFixedModelPointEquiv_natural K S f T p)).symm.trans
        ((numberFieldFixedModelPointEquiv K S Y T).symm_apply_apply (p ≫ f))
  rw [← heq]
  exact eY.symm.isProperMap.comp (hf.comp eX.isProperMap)

/-- The full-adele map of a proper number-field model morphism is proper. -/
theorem numberFieldFixedModel_proper :
    letI := numberFieldFixedModelAdelePointTopology K S X
    letI := numberFieldFixedModelAdelePointTopology K S Y
    IsProperMap
      (X := NumberFieldFixedModelAdelePoints K S X)
      (Y := NumberFieldFixedModelAdelePoints K S Y)
      (fun p : NumberFieldFixedModelAdelePoints K S X =>
        (p ≫ f : NumberFieldFixedModelAdelePoints K S Y)) := by
  let := numberFieldFixedModelAdelePointTopology K S X
  let := numberFieldFixedModelAdelePointTopology K S Y
  let : ∀ T, TopologicalSpace
      (RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T)) :=
    numberFieldFixedModelStageTopology K S X
  let : ∀ T, TopologicalSpace
      (RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevelOver K S T)) :=
    numberFieldFixedModelStageTopology K S Y
  exact isProperMap_of_final_stages
    (A := NumberFieldFixedModelAdelePoints K S X)
    (B := NumberFieldFixedModelAdelePoints K S Y)
    (fun T => RingPoint ((S : Set (FinitePlace K)).integer K) X (numberFieldAdeleLevelOver K S T))
    (fun T => RingPoint ((S : Set (FinitePlace K)).integer K) Y (numberFieldAdeleLevelOver K S T))
    (fun p => p ≫ f)
    (fun T => RingPoint.changeRing (X := X) (numberFieldAdeleLevelOverι K S T).hom)
    (fun T => RingPoint.changeRing (X := Y) (numberFieldAdeleLevelOverι K S T).hom)
    (fun T p => (p ≫ f : RingPoint ((S : Set (FinitePlace K)).integer K) Y
      (numberFieldAdeleLevelOver K S T)))
    (numberFieldFixedModelAdele_continuous K S f)
    (ringPointCoconeTopology_continuous_ι ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOverDiagram K S) X (numberFieldFixedModelStageTopology K S X)
      (numberFieldAdeleOverCocone K S))
    (numberFieldFixedModel_stage_injective K S Y)
    (fun _ _ => Category.assoc _ _ _)
    (numberFieldFixedModel_stage_preimage K S X Y f)
    (ringPointCoconeTopology_isClosed_iff ((S : Set (FinitePlace K)).integer K)
      (numberFieldAdeleLevelOverDiagram K S) Y (numberFieldFixedModelStageTopology K S Y)
      (numberFieldAdeleOverCocone K S))
    (adelicFixedModelFiniteType.2 K S Y).1
    (numberFieldFixedModel_stage_proper K S X Y f)

end NumberField

/-- The exact properness target for actual full-adele fixed-model points. -/
theorem adelicFixedModelProperMap : AdelicFixedModelProperMapStatement.{u} :=
  ⟨fun k F _ _ _ _ _ _ _ S X Y _ _ _ f _ => curvePlaceFixedModel_proper k F S X Y f,
    fun K _ _ S X Y _ _ _ f _ => numberFieldFixedModel_proper K S X Y f⟩

end Langlands.Global
