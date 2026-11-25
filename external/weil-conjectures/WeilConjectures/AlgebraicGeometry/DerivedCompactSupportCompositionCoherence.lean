/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

-- Internal comparison lemmas are shared through private imports.
set_option linter.privateModule false

/-!
# Structural coherence for three proper images and three open extensions

Source: Stacks Project, More on Étale Cohomology, Tag 0F7K, proof of
`lemma-pseudo-functor`.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

private lemma derived_triangle_assoc
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    [Abelian C₀] [Abelian C₁] [Abelian C₂] [Abelian C₃]
    [HasDerivedCategory C₀] [HasDerivedCategory C₁]
    [HasDerivedCategory C₂] [HasDerivedCategory C₃]
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₂ ⥤ C₃)
    (FG : C₀ ⥤ C₂) (GH : C₁ ⥤ C₃) (FGH : C₀ ⥤ C₃)
    [F.Additive] [G.Additive] [H.Additive]
    [FG.Additive] [GH.Additive] [FGH.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits FG] [PreservesFiniteColimits FG]
    [PreservesFiniteLimits GH] [PreservesFiniteColimits GH]
    [PreservesFiniteLimits FGH] [PreservesFiniteColimits FGH]
    (eFG : FG ≅ F ⋙ G) (eGH : GH ≅ G ⋙ H)
    (eF_GH : FGH ≅ F ⋙ GH) (eFG_H : FGH ≅ FG ⋙ H)
    (h : eF_GH ≪≫ Functor.isoWhiskerLeft F eGH =
      eFG_H ≪≫ Functor.isoWhiskerRight eFG H) :
    (Functor.mapDerivedCategoryTriangleIso eF_GH).hom ≫
        Functor.whiskerLeft F.mapDerivedCategory
          (Functor.mapDerivedCategoryTriangleIso eGH).hom =
      (Functor.mapDerivedCategoryTriangleIso eFG_H).hom ≫
        Functor.whiskerRight (Functor.mapDerivedCategoryTriangleIso eFG).hom
          H.mapDerivedCategory := by
  simp only [Functor.mapDerivedCategoryTriangleIso, Iso.trans_hom, Iso.symm_hom,
    Functor.whiskerLeft_comp, Functor.whiskerRight_comp, Category.assoc]
  rw [← Category.assoc (Functor.mapDerivedCategoryCompIso F GH).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerLeft,
    Category.assoc, ← Category.assoc (Functor.mapDerivedCategoryCompIso FG H).inv,
    ← Functor.mapDerivedCategoryNatIso_isoWhiskerRight]
  simp only [← Category.assoc]
  rw [← Functor.mapDerivedCategoryNatIso_trans, h,
    Functor.mapDerivedCategoryNatIso_trans]
  simp only [Category.assoc]
  rw [Functor.mapDerivedCategoryCompIso_assoc]

private lemma conjugate_triangle_assoc
    {C₀ C₁ C₂ C₃ : Type*}
    [Category C₀] [Category C₁] [Category C₂] [Category C₃]
    {F : C₀ ⥤ C₁} {G : C₁ ⥤ C₂} {H : C₂ ⥤ C₃}
    {FG : C₀ ⥤ C₂} {GH : C₁ ⥤ C₃} {FGH : C₀ ⥤ C₃}
    {RF : C₁ ⥤ C₀} {RG : C₂ ⥤ C₁} {RH : C₃ ⥤ C₂}
    {RFG : C₂ ⥤ C₀} {RGH : C₃ ⥤ C₁} {RFGH : C₃ ⥤ C₀}
    (af : F ⊣ RF) (ag : G ⊣ RG) (ah : H ⊣ RH)
    (afg : FG ⊣ RFG) (agh : GH ⊣ RGH) (afgh : FGH ⊣ RFGH)
    (eFG : FG ≅ F ⋙ G) (eGH : GH ≅ G ⋙ H)
    (eF_GH : FGH ≅ F ⋙ GH) (eFG_H : FGH ≅ FG ⋙ H)
    (h : eF_GH.hom ≫ Functor.whiskerLeft F eGH.hom =
      eFG_H.hom ≫ Functor.whiskerRight eFG.hom H) :
    Functor.whiskerLeft RH (conjugateEquiv (af.comp ag) afg eFG.hom) ≫
        conjugateEquiv (afg.comp ah) afgh eFG_H.hom =
      Functor.whiskerRight (conjugateEquiv (ag.comp ah) agh eGH.hom) RF ≫
        conjugateEquiv (af.comp agh) afgh eF_GH.hom := by
  have hm : (Functor.associator RH RG RF).hom ≫
      (Functor.whiskerLeft RH (conjugateEquiv (af.comp ag) afg eFG.hom) ≫
        conjugateEquiv (afg.comp ah) afgh eFG_H.hom) =
      Functor.whiskerRight (conjugateEquiv (ag.comp ah) agh eGH.hom) RF ≫
        conjugateEquiv (af.comp agh) afgh eF_GH.hom := by
    rw [← conjugateEquiv_associator_hom af ag ah,
      ← conjugateEquiv_whiskerRight (af.comp ag) afg ah,
      ← conjugateEquiv_whiskerLeft (ag.comp ah) agh af,
      conjugateEquiv_comp, conjugateEquiv_comp, conjugateEquiv_comp]
    congr 1
    apply NatTrans.ext
    funext K
    simpa only [NatTrans.comp_app, Functor.associator_hom_app, Category.comp_id] using
      (NatTrans.congr_app h K).symm
  apply NatTrans.ext
  funext K
  simpa only [NatTrans.comp_app, Functor.associator_hom_app, Category.id_comp] using
    NatTrans.congr_app hm K

namespace AlgebraicGeometry.Etale

private lemma push_comp_of_eq
    (A : Type (u + 1)) [CommRing A]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z)
    (hfg : fg = f ≫ g) :
    conjugateEquiv
      ((mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) g).comp
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f))
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) fg)
      (Functor.mapDerivedCategoryTriangleIso
        (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg)).hom =
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) f g).hom ≫
        eqToHom (by subst hfg; rfl) := by
  subst hfg
  rw [eqToHom_refl, Category.comp_id]
  rfl

private lemma push_derived_assoc
    (A : Type (u + 1)) [CommRing A]
    {X Y Z T : Scheme.{u}} (p : X ⟶ Y) (s : Y ⟶ Z) (t : Z ⟶ T) :
    Functor.whiskerLeft R((p)_*[ModuleCat.{u + 1} A])
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) s t).hom ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p (s ≫ t)).hom =
    Functor.whiskerRight
        (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) p s).hom
          R((t)_*[ModuleCat.{u + 1} A]) ≫
      (rightDerivedLowerStarComp (ModuleCat.{u + 1} A) (p ≫ s) t).hom ≫
        eqToHom (by simp only [Category.assoc]) := by
  let B := ModuleCat.{u + 1} A
  have hu : upperStarComp B (p ≫ s) t (p ≫ s ≫ t)
        (Category.assoc p s t).symm ≪≫
        Functor.isoWhiskerLeft (t)^*[B] (upperStarComp B p s) =
      upperStarComp B p (s ≫ t) ≪≫
        Functor.isoWhiskerRight (upperStarComp B s t) (p)^*[B] := by
    apply Iso.ext
    apply NatTrans.ext
    funext M
    simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
      Category.comp_id] using
      (NatTrans.congr_app (congrArg Iso.hom (upperStarComp_assoc B p s t)) M).symm
  have hd := derived_triangle_assoc (t)^*[B] (s)^*[B] (p)^*[B]
    (s ≫ t)^*[B] (p ≫ s)^*[B] (p ≫ s ≫ t)^*[B]
    (upperStarComp B s t) (upperStarComp B p s)
    (upperStarComp B (p ≫ s) t (p ≫ s ≫ t) (Category.assoc p s t).symm)
    (upperStarComp B p (s ≫ t)) hu
  have hm := conjugate_triangle_assoc
    (mapDerivedUpperStarLowerStarAdjunction B t)
    (mapDerivedUpperStarLowerStarAdjunction B s)
    (mapDerivedUpperStarLowerStarAdjunction B p)
    (mapDerivedUpperStarLowerStarAdjunction B (s ≫ t))
    (mapDerivedUpperStarLowerStarAdjunction B (p ≫ s))
    (mapDerivedUpperStarLowerStarAdjunction B (p ≫ s ≫ t))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp B s t))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp B p s))
    (Functor.mapDerivedCategoryTriangleIso
      (upperStarComp B (p ≫ s) t (p ≫ s ≫ t) (Category.assoc p s t).symm))
    (Functor.mapDerivedCategoryTriangleIso (upperStarComp B p (s ≫ t))) hd
  rw [push_comp_of_eq A, push_comp_of_eq A, push_comp_of_eq A,
    push_comp_of_eq A] at hm
  simpa only [eqToHom_refl, Category.comp_id, Category.assoc] using hm

attribute [local irreducible] rightDerivedLowerStarComp
  Functor.mapDerivedCategoryNatIso
  openImmersionLowerShriekComp Functor.rightDerivedFunctor Functor.mapDerivedCategory
  lowerStar openImmersionLowerShriek

end AlgebraicGeometry.Etale
