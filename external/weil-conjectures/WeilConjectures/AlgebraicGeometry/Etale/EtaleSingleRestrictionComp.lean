/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Etale.EtaleDegreeZeroHom
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSingleRestrictionFactors
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle

/-! # Composition of the degree-zero restriction comparison

Source: blueprint vector integration, compatibility with restriction.
(blueprint: lem-amb-etale-single-restriction-comp).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

attribute [local irreducible] _root_.DerivedCategory.singleFunctors
  Functor.leftDerivedFunctor upperStar

private theorem single_comp (A : Type (u + 1)) [CommRing A]
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) (w : T ⟶ S)
    (hw : w = p ≫ v) (P : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj P) ≫
      (ordinaryFinitePullback A p).map
        ((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v).hom.app P) ≫
      (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) p).hom.app
        ((upperStar (ModuleCat.{u + 1} A) v).obj P) =
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) w).hom.app P ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        ((upperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app P) := by
  exact leftDerivedUpperStarComp_hom_app_singleFunctor (ModuleCat.{u + 1} A) p v w hw P

private theorem single_comp_maps
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (R : D₀ ⥤ D₂)
    (sF : E₀ ⋙ P ≅ F ⋙ E₁) (sG : E₁ ⋙ Q ≅ G ⋙ E₂)
    (sH : E₀ ⋙ R ≅ H ⋙ E₂) (c : R ≅ P ⋙ Q) (k : H ≅ F ⋙ G)
    (X₀ : C₀) (X₁ : C₁) (X₂ : C₂)
    (a : F.obj X₀ ⟶ X₁) (b : G.obj X₁ ⟶ X₂) (d : H.obj X₀ ⟶ X₂)
    (hc : c.hom.app (E₀.obj X₀) ≫ Q.map (sF.hom.app X₀) ≫
        sG.hom.app (F.obj X₀) = sH.hom.app X₀ ≫ E₂.map (k.hom.app X₀))
    (hd : k.hom.app X₀ ≫ G.map a ≫ b = d) :
    c.hom.app (E₀.obj X₀) ≫ Q.map (sF.hom.app X₀ ≫ E₁.map a) ≫
        sG.hom.app X₁ ≫ E₂.map b = sH.hom.app X₀ ≫ E₂.map d := by
  have hn := sG.hom.naturality a
  simp only [Functor.comp_map] at hn
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hc]
  simp only [← E₂.map_comp, hd]

private theorem single_comp_comparisons
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (F F' : C₀ ⥤ C₁) (G G' : C₁ ⥤ C₂) (H H' : C₀ ⥤ C₂)
    (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (R : D₀ ⥤ D₂)
    (sF : E₀ ⋙ P ≅ F ⋙ E₁) (sG : E₁ ⋙ Q ≅ G ⋙ E₂)
    (sH : E₀ ⋙ R ≅ H ⋙ E₂) (c : R ≅ P ⋙ Q) (k : H ≅ F ⋙ G)
    (a : F ≅ F') (b : G ≅ G') (d : H ≅ H') (r : H' ≅ F' ⋙ G') (X : C₀)
    (hc : c.hom.app (E₀.obj X) ≫ Q.map (sF.hom.app X) ≫
        sG.hom.app (F.obj X) = sH.hom.app X ≫ E₂.map (k.hom.app X))
    (hd : d.hom.app X ≫ r.hom.app X =
      k.hom.app X ≫ G.map (a.hom.app X) ≫ b.hom.app (F'.obj X)) :
    c.hom.app (E₀.obj X) ≫
        Q.map ((sF ≪≫ Functor.isoWhiskerRight a E₁).hom.app X) ≫
        (sG ≪≫ Functor.isoWhiskerRight b E₂).hom.app (F'.obj X) =
      (sH ≪≫ Functor.isoWhiskerRight d E₂).hom.app X ≫ E₂.map (r.hom.app X) := by
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.map_comp, Category.assoc] using
    single_comp_maps E₀ E₁ E₂ F G H P Q R sF sG sH c k X (F'.obj X)
      (G'.obj (F'.obj X)) (a.hom.app X) (b.hom.app (F'.obj X))
      (d.hom.app X ≫ r.hom.app X) hc hd.symm

/-- The comparison between derived inverse image and restriction on degree-zero sheaves
respects the actual pullback and restriction compositors.
Source: blueprint vector integration, degree-zero restriction; the source composition
lemmas for derived pullback and upperStarIsoLocalizationRestriction.
(blueprint: lem-amb-etale-single-restriction-comp). -/
theorem etaleSingleRestrictionIso_comp (A : Type (u + 1)) [CommRing A]
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) (w : T ⟶ S)
    [Etale p] [Etale v] [Etale w] (hw : w = p ≫ v)
    (P : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) :
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app
        ((_root_.DerivedCategory.singleFunctor _ 0).obj P) ≫
      (ordinaryFinitePullback A p).map ((etaleSingleRestrictionIso A v).hom.app P) ≫
      (etaleSingleRestrictionIso A p).hom.app
        ((localizationRestriction (ModuleCat.{u + 1} A) v inferInstance).obj P) =
    (etaleSingleRestrictionIso A w).hom.app P ≫
      (_root_.DerivedCategory.singleFunctor _ 0).map
        ((localizationRestrictionComp' (ModuleCat.{u + 1} A) p v w hw).hom.app P) := by
  rw [etaleSingleRestrictionIso_eq A v, etaleSingleRestrictionIso_eq A p,
    etaleSingleRestrictionIso_eq A w]
  exact single_comp_comparisons
    (_root_.DerivedCategory.singleFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (_root_.DerivedCategory.singleFunctor
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (_root_.DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (upperStar (ModuleCat.{u + 1} A) v)
    (localizationRestriction (ModuleCat.{u + 1} A) v inferInstance)
    (upperStar (ModuleCat.{u + 1} A) p)
    (localizationRestriction (ModuleCat.{u + 1} A) p inferInstance)
    (upperStar (ModuleCat.{u + 1} A) w)
    (localizationRestriction (ModuleCat.{u + 1} A) w inferInstance)
    (ordinaryFinitePullback A v) (ordinaryFinitePullback A p) (ordinaryFinitePullback A w)
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) v)
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) p)
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) w)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw)
    (upperStarComp (ModuleCat.{u + 1} A) p v w hw)
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) v inferInstance)
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) p inferInstance)
    (upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} A) w inferInstance)
    (localizationRestrictionComp' (ModuleCat.{u + 1} A) p v w hw) P
    (single_comp A p v w hw P)
    (upperStarIsoLocalizationRestriction_comp (ModuleCat.{u + 1} A) p v w hw P)

end AlgebraicGeometry.Etale
