/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalDirectImageStalkClassMap
public import Mathlib.AlgebraicGeometry.AffineScheme

/-! # Independence of the top section class

Source: Stacks Project, Tags 01E4 and 01FB.
-/

@[expose] public section

universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives

private theorem homologyCounit_naturality
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (U : C ⥤ D) (S : D ⥤ C) [U.PreservesZeroMorphisms]
    [S.PreservesZeroMorphisms] [S.PreservesHomology]
    (ε : U ⋙ S ⟶ 𝟭 C) {A B : CochainComplex C ℕ} (l : A ⟶ B) (p : ℕ) :
    S.map (HomologicalComplex.homologyMap
      ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map l) p) ≫
      ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj B).sc p).mapHomologyIso S).inv ≫
        HomologicalComplex.homologyMap (ε.mapHomologicalComplex _ |>.app B) p =
    ((((U.mapHomologicalComplex (ComplexShape.up ℕ)).obj A).sc p).mapHomologyIso S).inv ≫
      HomologicalComplex.homologyMap (ε.mapHomologicalComplex _ |>.app A) p ≫
        HomologicalComplex.homologyMap l p := by
  simp only [HomologicalComplex.homologyMap]
  rw [ShortComplex.mapHomologyIso_inv_naturality_assoc]
  congr 1
  let H := HomologicalComplex.homologyFunctor C (ComplexShape.up ℕ) p
  change H.map ((S.mapHomologicalComplex (ComplexShape.up ℕ)).map
      ((U.mapHomologicalComplex (ComplexShape.up ℕ)).map l)) ≫
        H.map ((ε.mapHomologicalComplex _).app B) =
      H.map ((ε.mapHomologicalComplex _).app A) ≫ H.map l
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg H.map ((ε.mapHomologicalComplex (ComplexShape.up ℕ)).naturality l)

private theorem sectionComparison_naturality {Y : Scheme.{u}}
    {A B : CochainComplex Y.Modules ℕ} (l : A ⟶ B) (p : ℕ) :
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj)).map
      (HomologicalComplex.homologyMap
        (((SheafOfModules.forget.{u} Y.ringCatSheaf).mapHomologicalComplex
          (ComplexShape.up ℕ)).map l) p) ≫
        Scheme.Modules.sectionCohomologyComparison B p =
      Scheme.Modules.sectionCohomologyComparison A p ≫
        HomologicalComplex.homologyMap l p := by
  exact homologyCounit_naturality (SheafOfModules.forget.{u} Y.ringCatSheaf)
    (PresheafOfModules.sheafification (𝟙 Y.ringCatSheaf.obj))
    (PresheafOfModules.sheafificationAdjunction (𝟙 Y.ringCatSheaf.obj)).counit l p

private theorem sectionTheta_naturality {Y : Scheme.{u}}
    {A B : CochainComplex Y.Modules ℕ} (l : A ⟶ B) (p : ℕ) :
    HomologicalComplex.homologyMap
      (((SheafOfModules.forget.{u} Y.ringCatSheaf).mapHomologicalComplex
        (ComplexShape.up ℕ)).map l) p ≫ Scheme.Modules.sectionCohomologyTheta B p =
      Scheme.Modules.sectionCohomologyTheta A p ≫
        (SheafOfModules.forget.{u} Y.ringCatSheaf).map
          (HomologicalComplex.homologyMap l p) := by
  exact (PresheafOfModules.sheafificationAdjunction
    (𝟙 Y.ringCatSheaf.obj)).homEquiv_naturality_left_square _ _ _ _
      (sectionComparison_naturality l p)

-- Match global sections with top evaluation of the pushforward section complex.
private theorem topSection_naturality {Z Y : Scheme.{u}} (h : Z ⟶ Y)
    {G : Z.Modules} (R K : InjectiveResolution G) (l : R.cocomplex ⟶ K.cocomplex)
    (hl : R.ι.f 0 ≫ l.f 0 = K.ι.f 0) (p : ℕ) :
    Scheme.Modules.resolutionSectionClass R
      (((Scheme.Modules.pushforward h).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj R.cocomplex) ⊤ (Iso.refl _) p ≫
      Scheme.Modules.Hom.app
        (HomologicalComplex.homologyMap
          (((Scheme.Modules.pushforward h).mapHomologicalComplex
            (ComplexShape.up ℕ)).map l) p) ⊤ =
    Scheme.Modules.resolutionSectionClass K
      (((Scheme.Modules.pushforward h).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj K.cocomplex) ⊤ (Iso.refl _) p := by
  let P := (Scheme.Modules.pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)
  let U := (SheafOfModules.forget.{u} Y.ringCatSheaf).mapHomologicalComplex (ComplexShape.up ℕ)
  let E := PresheafOfModules.toPresheaf Y.ringCatSheaf.obj ⋙
    (evaluation Y.Opensᵒᵖ AddCommGrpCat.{u}).obj (op ⊤)
  have ht := congrArg E.map (sectionTheta_naturality (P.map l) p)
  simp only [Functor.map_comp] at ht
  have he := ShortComplex.mapHomologyIso_hom_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map
      (U.map (P.map l))) E
  let Γ := RingedSpace.globalSectionsFunctor Z.toRingedSpace
  let : Γ.Additive := RingedSpace.globalSectionsFunctor_additive Z.toRingedSpace
  let T := forget₂ (ModuleCat.{u} ((moduleRings Z.toRingedSpace).obj.obj (op ⊤)))
    AddCommGrpCat.{u}
  let L := Γ.mapHomologicalComplex (ComplexShape.up ℕ)
  have hs := ShortComplex.mapHomologyIso_inv_naturality
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℕ) p).map (L.map l)) T
  have hn := InjectiveResolution.isoRightDerivedObj_hom_naturality
    (𝟙 G) R K l (by simpa only [Category.id_comp] using hl) Γ p
  simp only [CategoryTheory.Functor.map_id, Category.id_comp] at hn
  have hg := congrArg T.map hn
  simp only [Functor.map_comp] at hg
  have hsquare := (CommSq.mk hs.symm).horiz_comp
    ((CommSq.mk he.symm).horiz_comp (CommSq.mk ht.symm))
  have hfinal := (Category.assoc (T.map (R.isoRightDerivedObj Γ p).hom) _ _).trans
    ((congrArg (T.map (R.isoRightDerivedObj Γ p).hom ≫ ·) hsquare.w).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hg.symm)))
  unfold Scheme.Modules.resolutionSectionClass
  simp only [Iso.refl_hom, CategoryTheory.Functor.map_id, Category.assoc]
  erw [Category.id_comp, Category.id_comp]
  simp only [Category.assoc] at hfinal
  convert hfinal using 1 <;> rfl


/-- The defined local class map can be computed on the top open using any
injective resolution of the pulled-back module.
Source: Stacks Project, Lemma 20.7.3 (Tag 01E4).
(blueprint: lem-weil-pbc-local-direct-image-stalk-class-top-comparison)

Proof: Let R be the fixed injective resolution in localDirectImage_stalk_class
and let h be the first projection. Lift the identity of the pulled-back module
from R to K by InjectiveResolution.desc. The augmentation equation gives
naturality of isoRightDerivedObj for global sections and for pushforward h.
The forgetful homology comparison is natural for this lift. Global sections of
the lift agree degreewise with top sections of its direct image. Naturality of
the exact-sheafification homology comparison and the sheafification counit makes
sectionCohomologyComparison natural; the adjunction makes sectionCohomologyTheta
natural. Evaluate at top and concatenate these squares. The map on homology of
the pushed lift cancels by naturality of isoRightDerivedObj.inv, and the derived
identity map is identity. This identifies the top class maps computed with R and
K. Compose with the top germ and evaluate at eta. The definition of
localDirectImage_stalk_class is exactly the first composite. No restriction to
a smaller open is involved, and the argument works for degree zero and zero
modules without assuming that theta is invertible on sections. -/
theorem localDirectImage_stalk_class_top_comparison
    {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) (F : X.Modules) (p : ℕ)
    (K : InjectiveResolution
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))
    (eta : (RingedSpace.moduleCohomology (pullback (Y.fromSpecStalk y) f).toRingedSpace p ⋙
      ModuleCat.restrictScalars
        ((Scheme.ΓSpecIso (CommRingCat.of (Y.presheaf.stalk y))).inv ≫
          (pullback.fst (Y.fromSpecStalk y) f).appTop).hom).obj
      ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F)) :
    localDirectImage_stalk_class f y F p eta =
      TopCat.Presheaf.germ
        ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
          (((Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)).rightDerived
            p).obj
            ((Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F))).presheaf
        ⊤ y (by trivial)
        (Scheme.Modules.Hom.app
          (K.isoRightDerivedObj
            (Scheme.Modules.pushforward (pullback.fst (Y.fromSpecStalk y) f)) p).inv ⊤
          (Scheme.Modules.resolutionSectionClass K
            (((Scheme.Modules.pushforward
              (pullback.fst (Y.fromSpecStalk y) f)).mapHomologicalComplex
              (ComplexShape.up ℕ)).obj K.cocomplex)
            ⊤ (Iso.refl _) p eta)) := by
  let G := (Scheme.Modules.tensorPullback (pullback.snd (Y.fromSpecStalk y) f)).obj F
  let R := injectiveResolution G
  let h := pullback.fst (Y.fromSpecStalk y) f
  let P := (Scheme.Modules.pushforward h).mapHomologicalComplex (ComplexShape.up ℕ)
  let l := InjectiveResolution.desc (𝟙 G) K R
  have hl : R.ι.f 0 ≫ l.f 0 = K.ι.f 0 := by
    simpa only [Category.id_comp] using InjectiveResolution.desc_commutes_zero (𝟙 G) K R
  have hn := InjectiveResolution.isoRightDerivedObj_inv_naturality
    (𝟙 G) R K l (by simpa only [Category.id_comp] using hl)
    (Scheme.Modules.pushforward h) p
  simp only [CategoryTheory.Functor.map_id, Category.comp_id] at hn
  let S := Scheme.Spec.obj (op (CommRingCat.of (Y.presheaf.stalk y)))
  let E : S.Modules ⥤ AddCommGrpCat.{u} :=
    SheafOfModules.forget.{u} S.ringCatSheaf ⋙ PresheafOfModules.toPresheaf _ ⋙
      (evaluation _ AddCommGrpCat.{u}).obj (op ⊤)
  have he := congrArg E.map hn
  simp only [Functor.map_comp] at he
  have hc := topSection_naturality h R K l hl p
  have hm :
      Scheme.Modules.resolutionSectionClass R (P.obj R.cocomplex) ⊤ (Iso.refl _) p ≫
        E.map (R.isoRightDerivedObj (Scheme.Modules.pushforward h) p).inv =
      Scheme.Modules.resolutionSectionClass K (P.obj K.cocomplex) ⊤ (Iso.refl _) p ≫
        E.map (K.isoRightDerivedObj (Scheme.Modules.pushforward h) p).inv := by
    rw [he, ← Category.assoc]
    exact congrArg (fun t ↦ t ≫
      E.map (K.isoRightDerivedObj (Scheme.Modules.pushforward h) p).inv) hc
  change Scheme.Modules.resolutionSectionClass R (P.obj R.cocomplex) ⊤ (Iso.refl _) p ≫
      Scheme.Modules.Hom.app (R.isoRightDerivedObj (Scheme.Modules.pushforward h) p).inv ⊤ =
    Scheme.Modules.resolutionSectionClass K (P.obj K.cocomplex) ⊤ (Iso.refl _) p ≫
      Scheme.Modules.Hom.app (K.isoRightDerivedObj (Scheme.Modules.pushforward h) p).inv ⊤
    at hm
  have hg := congrArg (fun t ↦ t ≫ TopCat.Presheaf.germ
    ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
      (((Scheme.Modules.pushforward h).rightDerived p).obj G)).presheaf
      ⊤ y (by trivial)) hm
  have hx := ConcreteCategory.congr_hom (C := AddCommGrpCat.{u}) hg eta
  change ((Scheme.Modules.resolutionSectionClass R (P.obj R.cocomplex) ⊤
    (Iso.refl _) p ≫ Scheme.Modules.Hom.app
      (R.isoRightDerivedObj (Scheme.Modules.pushforward h) p).inv ⊤ ≫
        TopCat.Presheaf.germ
          ((Scheme.Modules.pushforward (Y.fromSpecStalk y)).obj
            (((Scheme.Modules.pushforward h).rightDerived p).obj G)).presheaf
          ⊤ y (by trivial)) : _ ⟶ _) eta = _
  simp only [ConcreteCategory.comp_apply] at hx ⊢
  convert hx using 1

end AlgebraicGeometry
