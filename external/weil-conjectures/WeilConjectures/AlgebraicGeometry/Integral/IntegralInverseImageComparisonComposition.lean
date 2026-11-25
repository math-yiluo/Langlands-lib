/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SixFunctors.InverseImagePullbackComparisonDerived
public import WeilConjectures.PoincareDuality.Integral.IntegralPullbackComparisonRealization
public import WeilConjectures.SmoothPurity.Derived.DerivedPullbackTensorHom
import WeilConjectures.TraceFormula.Integral.IntegralPullbackResolutionMatching
import WeilConjectures.TraceFormula.Integral.IntegralPullbackReductionCounit
import WeilConjectures.CategoryTheory.ExactDerivedPasting.Word.ExactDerivedTransformationPasting

set_option linter.privateModule false

/-!
# Composition of the integral inverse-image comparison

The auxiliary compositor is fixed on sections, then applied termwise and localized.
The pullback compositor is exactly the recorded normalized realization, and kappa
is the recorded cone comparison evaluated on a derived object.

## References

* Stacks Project, Tags 03D6, 0D6D and 0941
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.sfAbSheafify WeilConjectures.sfAbBijective

universe u a b c
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private instance postcomposeCompContinuous
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    (proEtaleIsoPostcompose h ⋙ proEtaleIsoPostcompose k).IsContinuous
      (ProEt.topology Z) (ProEt.topology V) :=
  Functor.isContinuous_comp (proEtaleIsoPostcompose h) (proEtaleIsoPostcompose k)
    _ (ProEt.topology W) _

private instance mapCompContinuous
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    (MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale h) ⋙
      MorphismProperty.Over.map ⊤ (inferInstance : WeaklyEtale k)).IsContinuous
      (ProEt.topology Z) (ProEt.topology V) :=
  postcomposeCompContinuous h k

private theorem constantComposition
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (A : CommRingCat.{u + 1}) :
    (isoSectionwiseInverseImage h RingCat.{u + 1}).map
        (isoSectionwiseConstantMap.{u, u} k A) ≫ isoSectionwiseConstantMap.{u, u} h A =
      (Functor.sheafPushforwardContinuousNatTrans
        (MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom
        RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology V)).app
          ((sheafCompose (ProEt.topology V) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
            ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj A)) ≫
        isoSectionwiseConstantMap.{u, u} (h ≫ k) A := by
  let d := MorphismProperty.Over.mapComp (Q := ⊤)
    (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)
  let R := (sheafCompose (ProEt.topology V) (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
    ((constantSheaf (ProEt.topology V) CommRingCat.{u + 1}).obj A)
  let a := (Functor.sheafPushforwardContinuousNatTrans d.inv RingCat.{u + 1}
    (ProEt.topology Z) (ProEt.topology V)).app R ≫
    (isoSectionwiseInverseImage h RingCat.{u + 1}).map
      (isoSectionwiseConstantMap.{u, u} k A) ≫ isoSectionwiseConstantMap.{u, u} h A
  have ha : a = isoSectionwiseConstantMap.{u, u} (h ≫ k) A := by
    apply (isoSectionwiseConstantMap_existsUnique.{u, u} (h ≫ k) A).unique
    · intro U x
      change (isoSectionwiseConstantMap.{u, u} h A).hom.app (op U)
        ((isoSectionwiseConstantMap.{u, u} k A).hom.app (op ((proEtaleIsoPostcompose h).obj U))
          (R.obj.map (d.inv.app U).op
            ((toSheafify (ProEt.topology V) ((Functor.const V.ProEtᵒᵖ).obj A)).app
              (op ((proEtaleIsoPostcompose (h ≫ k)).obj U)) x))) = _
      have hn := congrArg (fun f ↦ f x)
        ((toSheafify (ProEt.topology V)
          ((Functor.const V.ProEtᵒᵖ).obj A)).naturality (d.inv.app U).op)
      dsimp at hn
      erw [← hn]
      exact (congrArg ((isoSectionwiseConstantMap.{u, u} h A).hom.app (op U))
          ((isoSectionwiseConstantMap_existsUnique.{u, u} k A).exists.choose_spec
            ((proEtaleIsoPostcompose h).obj U) x)).trans
        ((isoSectionwiseConstantMap_existsUnique.{u, u} h A).exists.choose_spec U x)
    · exact (isoSectionwiseConstantMap_existsUnique.{u, u} (h ≫ k) A).exists.choose_spec
  rw [← ha]
  ext U x
  change _ = (isoSectionwiseConstantMap.{u, u} h A).hom.app U
    ((isoSectionwiseConstantMap.{u, u} k A).hom.app _
      (R.obj.map (d.inv.app U.unop).op (R.obj.map (d.hom.app U.unop).op x)))
  rw [← RingCat.comp_apply, ← R.obj.map_comp, ← op_comp, d.inv_hom_id_app]
  rw [op_id, R.obj.map_id]
  rfl

private theorem completedComposition
    {Z W V : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k] :
    (isoSectionwiseInverseImage h RingCat.{u + 1}).map
        (inverseImageCompletedCoefficientMap l E k) ≫
      inverseImageCompletedCoefficientMap l E h =
      (Functor.sheafPushforwardContinuousNatTrans
        (MorphismProperty.Over.mapComp (Q := ⊤)
          (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom
        RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology V)).app
          (completedIntegralCoefficientSheafUnrestricted l E V) ≫
        inverseImageCompletedCoefficientMap l E (h ≫ k) := by
  let F := isoSectionwiseInverseImage h RingCat.{u + 1}
  let T := Functor.sheafPushforwardContinuousNatTrans
    (MorphismProperty.Over.mapComp (Q := ⊤)
      (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom
    RingCat.{u + 1} (ProEt.topology Z) (ProEt.topology V)
  apply limit.hom_ext
  intro n
  simp only [Category.assoc, inverseImageCompletedCoefficientMap, limit.lift_π]
  change F.map (inverseImageCompletedCoefficientMap l E k) ≫
    (F.map (limit.π (integralCoefficientSheafSystem l E W) n) ≫
      inverseImageFiniteCoefficientMap l E h n.unop) = _
  rw [← Category.assoc, ← F.map_comp]
  simp only [inverseImageCompletedCoefficientMap, limit.lift_π]
  dsimp only [inverseImageCompletedCoefficientComponent]
  rw [F.map_comp, Category.assoc, constantComposition]
  have hn := T.naturality (limit.π (integralCoefficientSheafSystem l E V) n)
  change F.map ((isoSectionwiseInverseImage k RingCat.{u + 1}).map
      (limit.π (integralCoefficientSheafSystem l E V) n)) ≫ _ = _ at hn
  rw [← Category.assoc]
  simpa only [Category.assoc, completedIntegralCoefficientSheafUnrestricted,
    integralCoefficientSheafSystem, Functor.ofOpSequence, Functor.ofSequence,
    Functor.leftOp, integralCoefficientSheaf, isoSectionwiseInverseImage,
    proEtaleIsoPostcompose, T] using
    congrArg (fun f ↦ f ≫ inverseImageFiniteCoefficientMap l E (h ≫ k) n.unop) hn

private theorem counitIdentity_transport
    {A B C : Type*} [Category A] [Category B] [Category C]
    (H F : A ⥤ B) (L : B ⥤ C) (T : A ⥤ C)
    (γ : F ⋙ L ⟶ T) (β : H ⋙ L ⟶ T)
    {X Y : A} (r : X ≅ Y) (aX : H.obj X ⟶ F.obj X) (aY : H.obj Y ⟶ F.obj Y)
    (ha : H.map r.hom ≫ aY = aX ≫ F.map r.hom)
    (hX : L.map aX ≫ γ.app X = β.app X) :
    L.map aY ≫ γ.app Y = β.app Y := by
  apply (cancel_epi (L.map (H.map r.hom))).1
  calc
    _ = L.map (H.map r.hom ≫ aY) ≫ γ.app Y := by
      rw [Functor.map_comp, Category.assoc]
    _ = L.map (aX ≫ F.map r.hom) ≫ γ.app Y := by rw [ha]
    _ = L.map aX ≫ γ.app X ≫ T.map r.hom := by
      rw [Functor.map_comp, Category.assoc, ← γ.naturality]
      rfl
    _ = (H ⋙ L).map r.hom ≫ β.app Y := by
      rw [← Category.assoc, hX, β.naturality]
    _ = _ := rfl

private theorem chosenResolution_formula
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (M : DerivedCategory (integralTowerModules l E W)) :
    ∃ (K : CochainComplex (integralTowerModules l E W) ℤ)
      (eK : DerivedCategory.Q.obj K ≅ M)
      (P : (integralOperationsGoodComplex l E W).FullSubcategory)
      (q : P.obj ⟶ K) (hq : QuasiIso q),
      let := hq
      inverseImagePullbackComparisonDerived l E h hZ hW M =
        (inverseImageIntegralDerived l E h).map eK.inv ≫
        (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app K ≫
        inv (DerivedCategory.Q.map
          (((inverseImageIntegralModules l E h).mapHomologicalComplex (.up ℤ)).map q)) ≫
        DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P.obj) ≫
        (integralDerivedPullbackComparison l E h).inv.app P ≫
        (integralDerivedPullback l E h).map (DerivedCategory.Q.map q) ≫
        (integralDerivedPullback l E h).map eK.hom := by
  unfold inverseImagePullbackComparisonDerived
  extract_lets K e hp P q hq
  let P' : (integralOperationsGoodComplex.{u, u} l E W).FullSubcategory :=
    ⟨P, hq.1, fun i ↦ (exactFunctor _ _).prop_of_iso
      (@SheafOfModules.siteSheafTensorRightIso.{u + 1, u, u + 1}
        W.ProEt inferInstance (essentiallySmallSelf.{0, u, u + 1} _)
        (ProEt.topology W) (completedIntegralCommRingSheafUnrestricted.{u, u} l E W)
        (P.X i)).symm (hq.2.1 i)⟩
  refine ⟨K, e, P', q, hq.2.2.1, ?_⟩
  simp only [inverseImagePullbackComparison, Category.assoc]
  rfl

private theorem heq_apply {A A' : Type a} {B B' : Type b} {f : A → B} {g : A' → B'}
    (hB : B = B') (hf : HEq f g) {x : A} {x' : A'} (hx : HEq x x') :
    HEq (f x) (g x') := by
  cases hB
  exact heq_of_eq (congr_heq hf hx)

private theorem restrictedSection_map
    (X : Scheme.{u}) {M N : coefficientSequenceModules l E X} (f : M ⟶ N)
    (n : ℕ) (U : X.ProEtᵒᵖ) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l E X).map f).app (op n)).val.app U
        (integralComparisonRestrictedSection l E X M n U x) =
      integralComparisonRestrictedSection l E X N n U
        (f.val.app (op (n, U.unop)) x) := by
  have h := (coefficientSequenceRestriction_exists l E X).exists.choose_spec.2.2 f n U
  apply eq_of_heq
  exact (heq_apply (integralComparisonRestrictedSectionType l E X N n U) h
    (cast_heq _ x)).trans (cast_heq _ _).symm

private theorem cast_map
    {A : Type*} [Category A] {P Q : A ⥤ AddCommGrpCat.{u + 1}} (e : P = Q)
    {U V : A} (f : U ⟶ V) (x : Q.obj U) :
    P.map f (cast (congrArg (fun (P : A ⥤ AddCommGrpCat.{u + 1}) ↦ ↥(P.obj U)) e).symm x) =
      cast (congrArg (fun (P : A ⥤ AddCommGrpCat.{u + 1}) ↦ ↥(P.obj V)) e).symm (Q.map f x) := by
  subst e
  rfl

private theorem restrictedSection_naturality
    (X : Scheme.{u}) (M : coefficientSequenceModules l E X) (n : ℕ)
    {U V : X.ProEtᵒᵖ} (f : U ⟶ V) (x : M.val.obj (op (n, U.unop))) :
    (((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.map f
        (integralComparisonRestrictedSection l E X M n U x) =
      integralComparisonRestrictedSection l E X M n V
        (M.val.map (Prod.mkHom (𝟙 n) f.unop).op x) := by
  have e : (((coefficientSequenceRestriction l E X).obj M).obj (op n)).val.presheaf =
      (Prod.sectR n X.ProEt).op ⋙ M.val.presheaf := by
    change (((coefficientSequenceRestriction_exists l E X).exists.choose.obj M).obj
      (op n)).val.presheaf = _
    rw [(coefficientSequenceRestriction_exists l E X).exists.choose_spec.1 M n]
    rfl
  exact cast_map e f x

private theorem sequenceGenerator_composition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V)
    (M : coefficientSequenceModules l E V) (n : ℕ) (U : V.ProEt)
    (x : M.val.obj (op (n, U))) :
    ((integralComparisonSequenceComposition l E h k).hom.app M).val.app
        (op (n, (proEtaleBaseChange (h ≫ k)).obj U))
        (integralComparisonSequenceGenerator l E (h ≫ k) M n U x) =
      ((integralComparisonSequencePullback l E h).obj
          ((integralComparisonSequencePullback l E k).obj M)).val.map
        (Prod.mkHom (𝟙 n) ((MorphismProperty.Over.pullbackComp h k).hom.app U)).op
        (integralComparisonSequenceGenerator l E h
          ((integralComparisonSequencePullback l E k).obj M) n
          ((proEtaleBaseChange k).obj U)
          (integralComparisonSequenceGenerator l E k M n U x)) := by
  let Ak := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E k)
  let Ah := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E h)
  let Aj := Adjunction.ofIsRightAdjoint (integralComparisonSequenceDirectImage l E (h ≫ k))
  obtain ⟨c, hc, hs⟩ :=
    (integralComparisonSequenceComposition_existsUnique l E h k).exists.choose_spec
  have ht := unit_conjugateEquiv (Ak.comp Ah) Aj
    (integralComparisonSequenceComposition l E h k).hom M
  have hh : conjugateEquiv (Ak.comp Ah) Aj
      (integralComparisonSequenceComposition l E h k).hom = c.hom :=
    congrArg Iso.hom hc
  rw [hh] at ht
  have hh := congrArg (fun f ↦ f.val.app (op (n, U)) x) ht
  change (c.hom.app _).val.app (op (n, U))
      (integralComparisonSequenceGenerator l E h
        ((integralComparisonSequencePullback l E k).obj M) n
        ((proEtaleBaseChange k).obj U)
        (integralComparisonSequenceGenerator l E k M n U x)) =
    ((integralComparisonSequenceComposition l E h k).hom.app M).val.app
      (op (n, (proEtaleBaseChange (h ≫ k)).obj U))
      (integralComparisonSequenceGenerator l E (h ≫ k) M n U x) at hh
  rw [hs] at hh
  exact hh.symm

private theorem sequenceGenerator_naturality
    {Y X : Scheme.{u}} (g : X ⟶ Y)
    (M : coefficientSequenceModules l E Y) (n : ℕ)
    {U V : Y.ProEt} (f : U ⟶ V) (x : M.val.obj (op (n, V))) :
    integralComparisonSequenceGenerator l E g M n U
        (M.val.map (Prod.mkHom (𝟙 n) f).op x) =
      ((integralComparisonSequencePullback l E g).obj M).val.map
        (Prod.mkHom (𝟙 n) ((proEtaleBaseChange g).map f)).op
        (integralComparisonSequenceGenerator l E g M n V x) := by
  exact congrArg (fun z ↦ z x)
    (((Adjunction.ofIsRightAdjoint
      (integralComparisonSequenceDirectImage l E g)).unit.app M).val.naturality
      (Prod.mkHom (𝟙 n) f).op)

private theorem comma_composition
    {V W Z : Scheme.{u}} (h : Z ⟶ W) (k : W ⟶ V) [IsIso h] [IsIso k]
    (U : Z.ProEt) :
    proEtaleIsoCommaArrow (h ≫ k) U ≫
        (proEtaleBaseChange (h ≫ k)).map
          ((MorphismProperty.Over.mapComp (Q := ⊤)
            (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U) ≫
        (MorphismProperty.Over.pullbackComp h k).hom.app
          ((proEtaleIsoPostcompose k).obj ((proEtaleIsoPostcompose h).obj U)) =
      proEtaleIsoCommaArrow h U ≫
        (proEtaleBaseChange h).map
          (proEtaleIsoCommaArrow k ((proEtaleIsoPostcompose h).obj U)) := by
  let A := (proEtaleIsoPostcompose k).obj ((proEtaleIsoPostcompose h).obj U)
  have hc : ((MorphismProperty.Over.pullbackComp h k).hom.app A).left ≫
      pullback.fst (pullback.snd A.hom k) h ≫ pullback.fst A.hom k =
      pullback.fst A.hom (h ≫ k) := by
    change (pullback.congrHom _ _ ≪≫ (pullbackLeftPullbackSndIso A.hom k h).symm).hom ≫
      pullback.fst _ _ ≫ pullback.fst _ _ = _
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
      pullbackLeftPullbackSndIso_inv_fst]
    simp
  apply MorphismProperty.Over.Hom.ext
  change (proEtaleIsoCommaArrow (h ≫ k) U).left ≫
      ((proEtaleBaseChange (h ≫ k)).map _).left ≫
      ((MorphismProperty.Over.pullbackComp h k).hom.app A).left =
    (proEtaleIsoCommaArrow h U).left ≫
      ((proEtaleBaseChange h).map _).left
  apply (cancel_mono (pullback.fst (pullback.snd A.hom k) h)).1
  apply (cancel_mono (pullback.fst A.hom k)).1
  simp only [Category.assoc]
  erw [hc]
  have hm : ((proEtaleBaseChange (h ≫ k)).map
      ((MorphismProperty.Over.mapComp (Q := ⊤)
        (inferInstance : WeaklyEtale h) (inferInstance : WeaklyEtale k)).hom.app U)).left ≫
        pullback.fst A.hom (h ≫ k) =
      pullback.fst ((proEtaleIsoPostcompose (h ≫ k)).obj U).hom (h ≫ k) := by
    dsimp only [proEtaleBaseChange]
    rw [MorphismProperty.Over.pullback_map_left]
    erw [pullback.lift_fst]
    simp only [MorphismProperty.Over.mapComp_hom_app_left]
    exact Category.comp_id _
  rw [hm]
  have hf {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (T : X.ProEt) :
      (proEtaleIsoCommaArrow f T).left ≫
        pullback.fst ((proEtaleIsoPostcompose f).obj T).hom f = 𝟙 T.left := by
    dsimp only [proEtaleIsoCommaArrow, MorphismProperty.Over.mapPullbackAdj]
    change pullback.lift (𝟙 T.left) T.hom _ ≫ pullback.fst (T.hom ≫ f) f = _
    exact pullback.lift_fst _ _ _
  rw [hf]
  dsimp only [proEtaleBaseChange]
  rw [MorphismProperty.Over.pullback_map_left]
  erw [pullback.lift_fst_assoc]
  rw [Category.assoc, hf, Category.comp_id, hf]

private theorem comparison_counit
    {W Z : Scheme.{u}} (h : Z ⟶ W) [IsIso h]
    (hW : ∀ w : W, IsUnit (l : W.presheaf.stalk w))
    (hZ : ∀ z : Z, IsUnit (l : Z.presheaf.stalk z))
    (S : CoefficientDerivedSystemCalculus l E W)
    (ρ : IntegralComparisonRoosModel l E Z)
    (F : IntegralComparisonPullbackModel l E h S ρ)
    (M : DerivedCategory (integralTowerModules l E W)) :
    (integralComparisonConstantTower l E Z).map
        (inverseImagePullbackComparisonDerived l E h hZ hW M ≫
          F.realization.hom.app M) ≫
        (integralComparisonTowerCounit l E Z).app
          ((coefficientSequenceDerivedRestriction l E Z).obj
            ((integralComparisonDerivedSequencePullback l E h).obj (S.reduction.obj M))) =
      (integralTowerInverseImageDiagonal l E h).hom.app M ≫
        (integralDerivedTowerInverseImage l E h).map
          ((integralComparisonConstantTower l E W).map (S.adjunction.unit.app M) ≫
            (integralComparisonTowerCounit l E W).app
              ((coefficientSequenceDerivedRestriction l E W).obj (S.reduction.obj M))) ≫
        (integralDerivedTowerInverseImageUnit l E h).hom.app (S.reduction.obj M) := by
  let a := inverseImagePullbackComparisonDerived l E h hZ hW M
  let e := F.realization.hom.app M
  let δ := (integralComparisonConstantTower l E W).map (S.adjunction.unit.app M) ≫
    (integralComparisonTowerCounit l E W).app
      ((coefficientSequenceDerivedRestriction l E W).obj (S.reduction.obj M))
  let H := inverseImageIntegralDerived l E h
  let ΔW := integralComparisonConstantTower l E W
  let ΔZ := integralComparisonConstantTower l E Z
  let U (X : Scheme.{u}) := coefficientSequenceDerivedRestriction.{u, u} l E X
  let B := integralComparisonDerivedSequencePullback l E h
  let Ht := integralDerivedTowerInverseImage l E h
  let d : ΔW ⟶ S.reduction ⋙ U W :=
    Functor.whiskerRight S.adjunction.unit ΔW ≫
      Functor.whiskerLeft (S.reduction ⋙ U W) (integralComparisonTowerCounit l E W)
  let γ : integralDerivedPullback l E h ⋙ ΔZ ⟶ S.reduction ⋙ B ⋙ U Z :=
    Functor.whiskerRight F.realization.hom ΔZ ≫
      Functor.whiskerLeft (S.reduction ⋙ B ⋙ U Z) (integralComparisonTowerCounit l E Z)
  let β : H ⋙ ΔZ ⟶ S.reduction ⋙ B ⋙ U Z :=
    (integralTowerInverseImageDiagonal l E h).hom ≫
      Functor.whiskerRight d Ht ≫
      Functor.whiskerLeft S.reduction (integralDerivedTowerInverseImageUnit l E h).hom
  obtain ⟨K, eK, P', q, hq, hformula⟩ :=
    chosenResolution_formula l E h hW hZ M
  let := hq
  let P := P'.obj
  let r : DerivedCategory.Q.obj P ≅ M := asIso (DerivedCategory.Q.map q) ≪≫ eK
  let aP := (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.app P ≫
    DerivedCategory.Q.map (inverseImageRoosComparisonComplex l E h P) ≫
      (integralDerivedPullbackComparison l E h).inv.app P'
  have hP : ΔZ.map aP ≫ γ.app (DerivedCategory.Q.obj P) =
      β.app (DerivedCategory.Q.obj P) := by
    simpa only [γ, β, d, aP, P, H, ΔW, ΔZ, U, B, Ht, e, δ,
      Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      NatTrans.comp_app, Functor.map_comp, Category.assoc] using
      integralPullbackKFlatReductionCounit l E h S ρ F P'
  have ha : H.map r.hom ≫ a = aP ≫ (integralDerivedPullback l E h).map r.hom := by
    rw [show a = _ from hformula]
    simp only [r, Iso.trans_hom, asIso_hom, Functor.map_comp, Category.assoc]
    rw [← Category.assoc (H.map eK.hom), ← H.map_comp,
      eK.hom_inv_id, H.map_id, Category.id_comp]
    erw [← Category.assoc (H.map (DerivedCategory.Q.map q)),
      (inverseImageIntegralModules l E h).mapDerivedCategoryFactors.hom.naturality q]
    simp only [Functor.comp_map, Category.assoc, IsIso.hom_inv_id_assoc, aP, P]
  have ht := counitIdentity_transport H (integralDerivedPullback l E h) ΔZ
    (S.reduction ⋙ B ⋙ U Z) γ β r aP a ha hP
  simpa only [γ, β, d, H, ΔW, ΔZ, U, B, Ht, e, δ,
    Functor.comp_obj, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    NatTrans.comp_app, Functor.map_comp, Category.assoc] using ht

section AbstractPasting

variable {A0 A1 A2 A3 A4 A5 : Type a}
  [Category.{b} A0] [Category.{b} A1] [Category.{b} A2]
  [Category.{b} A3] [Category.{b} A4] [Category.{b} A5]
  [Abelian A0] [Abelian A1] [Abelian A2] [Abelian A3] [Abelian A4] [Abelian A5]
  [HasDerivedCategory.{c} A0] [HasDerivedCategory.{c} A1] [HasDerivedCategory.{c} A2]
  [HasDerivedCategory.{c} A3] [HasDerivedCategory.{c} A4] [HasDerivedCategory.{c} A5]

end AbstractPasting

end AlgebraicGeometry.ProEtale
