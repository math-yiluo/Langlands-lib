/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Etale.EtaleDegreeZeroHom
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSingleRestrictionComp

/-! # The inverse degree-zero Hom correspondence and restriction

Source: blueprint vector integration, compatibility with restriction.
(blueprint: lem-amb-etale-degree-zero-hom-restriction).
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

private theorem restriction_conjugation
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (R : D₀ ⥤ D₂)
    (ηv : E₀ ⋙ P ≅ F ⋙ E₁) (ηp : E₁ ⋙ Q ≅ G ⋙ E₂)
    (ηw : E₀ ⋙ R ≅ H ⋙ E₂) (c : R ≅ P ⋙ Q) (r : H ≅ F ⋙ G)
    (hc : ∀ X, c.hom.app (E₀.obj X) ≫ Q.map (ηv.hom.app X) ≫
      ηp.hom.app (F.obj X) = ηw.hom.app X ≫ E₂.map (r.hom.app X))
    {K : D₀} {M N : C₀} (α : K ≅ E₀.obj M) (ψ : F.obj M ⟶ F.obj N) :
    R.map α.hom ≫ ηw.hom.app M ≫
        E₂.map (r.hom.app M ≫ G.map ψ ≫ r.inv.app N) ≫ ηw.inv.app N =
      c.hom.app K ≫ Q.map
        (P.map α.hom ≫ ηv.hom.app M ≫ E₁.map ψ ≫ ηv.inv.app N) ≫
        c.inv.app (E₀.obj N) := by
  have hm (X : C₀) :
      c.hom.app (E₀.obj X) ≫ Q.map (ηv.hom.app X) =
        ηw.hom.app X ≫ E₂.map (r.hom.app X) ≫ ηp.inv.app (F.obj X) := by
    simpa only [Iso.app_inv, Category.assoc] using
      (Iso.eq_comp_inv (ηp.app (F.obj X))
        (f := ηw.hom.app X ≫ E₂.map (r.hom.app X))
        (g := c.hom.app (E₀.obj X) ≫ Q.map (ηv.hom.app X))).2
          (by simpa only [Iso.app_hom, Category.assoc] using hc X)
  have hq : Q.map (ηv.inv.app N) ≫ c.inv.app (E₀.obj N) =
      ηp.hom.app (F.obj N) ≫ E₂.map (r.inv.app N) ≫ ηw.inv.app N := by
    have he : c.app (E₀.obj N) ≪≫ Q.mapIso (ηv.app N) ≪≫ ηp.app (F.obj N) =
        ηw.app N ≪≫ E₂.mapIso (r.app N) := by
      apply Iso.ext
      exact hc N
    have hi := congrArg Iso.inv he
    apply (cancel_epi (ηp.inv.app (F.obj N))).mp
    simpa only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv, Category.assoc,
      Iso.inv_hom_id_app_assoc] using hi
  have ha := c.hom.naturality α.hom
  have hn := ηp.hom.naturality ψ
  simp only [Functor.comp_map] at ha hn
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% ha, reassoc_of% (hm M), hq, reassoc_of% hn]
  simp only [Iso.inv_hom_id_app_assoc]

private theorem hom_comp_iso_symm_apply
    {C C' D D' : Type*} [Category C] [Category C'] [Category D] [Category D']
    (E : C ⥤ D) (E' : C' ⥤ D') (hE' : E'.FullyFaithful)
    (P : D ⥤ D') (F : C ⥤ C') (η : E ⋙ P ≅ F ⋙ E')
    {K : D} {M N : C} (α : K ≅ E.obj M) (ψ : F.obj M ⟶ F.obj N) :
    (fullyFaithfulHomEquivOfCompIso E E' hE' P F η α).symm ψ =
      P.map α.hom ≫ η.hom.app M ≫ E'.map ψ ≫ η.inv.app N := by
  unfold fullyFaithfulHomEquivOfCompIso
  rw [fullyFaithfulHomEquivOfIsos_symm_apply]
  simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, Category.assoc]

private theorem hom_restriction_symm
    {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
    [Category C₀] [Category C₁] [Category C₂]
    [Category D₀] [Category D₁] [Category D₂]
    (E₀ : C₀ ⥤ D₀) (E₁ : C₁ ⥤ D₁) (E₂ : C₂ ⥤ D₂)
    (hE₁ : E₁.FullyFaithful) (hE₂ : E₂.FullyFaithful)
    (F : C₀ ⥤ C₁) (G : C₁ ⥤ C₂) (H : C₀ ⥤ C₂)
    (P : D₀ ⥤ D₁) (Q : D₁ ⥤ D₂) (R : D₀ ⥤ D₂)
    (ηv : E₀ ⋙ P ≅ F ⋙ E₁) (ηp : E₁ ⋙ Q ≅ G ⋙ E₂)
    (ηw : E₀ ⋙ R ≅ H ⋙ E₂) (c : R ≅ P ⋙ Q) (r : H ≅ F ⋙ G)
    (hc : ∀ X, c.hom.app (E₀.obj X) ≫ Q.map (ηv.hom.app X) ≫
      ηp.hom.app (F.obj X) = ηw.hom.app X ≫ E₂.map (r.hom.app X))
    {K : D₀} {M N : C₀} (α : K ≅ E₀.obj M) (ψ : F.obj M ⟶ F.obj N) :
    (fullyFaithfulHomEquivOfCompIso E₀ E₂ hE₂ R H ηw α).symm
        (r.hom.app M ≫ G.map ψ ≫ r.inv.app N) =
      c.hom.app K ≫
        Q.map ((fullyFaithfulHomEquivOfCompIso E₀ E₁ hE₁ P F ηv α).symm ψ) ≫
        c.inv.app (E₀.obj N) := by
  rw [hom_comp_iso_symm_apply, hom_comp_iso_symm_apply]
  exact restriction_conjugation E₀ E₁ E₂ F G H P Q R ηv ηp ηw c r hc α ψ

/-- The inverse degree-zero Hom correspondence commutes with the specified etale
restriction compositor. This applies to any source isomorphic to a sheaf in degree zero.
Source: blueprint vector integration, exact inverse image and degree-zero restriction.
(blueprint: lem-amb-etale-degree-zero-hom-restriction). -/
theorem etaleDegreeZeroHomEquiv_symm_compRestriction (A : Type (u + 1)) [CommRing A]
    {T U S : Scheme.{u}} (p : T ⟶ U) (v : U ⟶ S) (w : T ⟶ S)
    [Etale p] [Etale v] [Etale w] (hw : w = p ≫ v)
    {K : DerivedCategoryModule A S}
    {M Q : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)}
    (α : K ≅ (_root_.DerivedCategory.singleFunctor _ 0).obj M)
    (ψ : (localizationRestriction (ModuleCat.{u + 1} A) v inferInstance).obj M ⟶
      (localizationRestriction (ModuleCat.{u + 1} A) v inferInstance).obj Q) :
    (etaleDegreeZeroHomEquiv A w α).symm (compRestriction v p w hw ψ) =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw).hom.app K ≫
        (ordinaryFinitePullback A p).map ((etaleDegreeZeroHomEquiv A v α).symm ψ) ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw).inv.app
          ((_root_.DerivedCategory.singleFunctor _ 0).obj Q) := by
  unfold etaleDegreeZeroHomEquiv compRestriction
  exact hom_restriction_symm
    (_root_.DerivedCategory.singleFunctor
      (Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (_root_.DerivedCategory.singleFunctor
      (Sheaf U.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (_root_.DerivedCategory.singleFunctor
      (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A)) 0)
    (_root_.DerivedCategory.fullyFaithfulSingleFunctor 0)
    (_root_.DerivedCategory.fullyFaithfulSingleFunctor 0)
    (localizationRestriction (ModuleCat.{u + 1} A) v inferInstance)
    (localizationRestriction (ModuleCat.{u + 1} A) p inferInstance)
    (localizationRestriction (ModuleCat.{u + 1} A) w inferInstance)
    (ordinaryFinitePullback A v) (ordinaryFinitePullback A p) (ordinaryFinitePullback A w)
    (etaleSingleRestrictionIso A v) (etaleSingleRestrictionIso A p)
    (etaleSingleRestrictionIso A w)
    (leftDerivedUpperStarComp (ModuleCat.{u + 1} A) p v w hw)
    (localizationRestrictionComp' (ModuleCat.{u + 1} A) p v w hw)
    (fun X ↦ etaleSingleRestrictionIso_comp A p v w hw X) α ψ

end AlgebraicGeometry.Etale
