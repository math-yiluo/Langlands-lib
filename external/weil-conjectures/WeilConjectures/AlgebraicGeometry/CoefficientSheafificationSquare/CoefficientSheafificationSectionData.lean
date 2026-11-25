/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement

/-! # The abelian counit comparisons for a coefficient square

(blueprint: def-weil-pbc-coefficient-sheafification-section-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme.CoefficientSheafificationSquare

abbrev forgetIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    (B R : Type (u + 1)) [CommRing B] [CommRing R] (q : R →+* B)
    (S : Sheaf J RingCat.{u + 1})
    (a : (Functor.const Cᵒᵖ).obj (RingCat.of R) ⟶ S.obj)
    [Presheaf.IsLocallyInjective J a] [Presheaf.IsLocallySurjective J a]
    [HasSheafify J AddCommGrpCat.{u + 1}] [J.WEqualsLocallyBijective AddCommGrpCat.{u + 1}] :
    (sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
      (sheafToPresheaf J (ModuleCat.{u + 1} R) ⋙
        ProEtale.finiteCoefficientModulePresheaf C R ⋙
        PresheafOfModules.sheafification a)) ⋙ SheafOfModules.toSheaf S ≅
      sheafCompose J (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1}) := by
  let G := sheafCompose J (forget₂ (ModuleCat.{u + 1} B) AddCommGrpCat.{u + 1})
  change (G ⋙ sheafToPresheaf _ _) ⋙ presheafToSheaf _ _ ≅ G
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft G (asIso (sheafificationAdjunction J AddCommGrpCat.{u + 1}).counit) ≪≫
      Functor.rightUnitor G

abbrev fixedRestrictForgetIso
    {C : Type (u + 1)} [Category.{u} C] (J : GrothendieckTopology C)
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (q : R →+* S) :
    sheafCompose J (ModuleCat.restrictScalars.{u + 1, u + 1, u + 1} q) ⋙
        sheafCompose J (forget₂ (ModuleCat.{u + 1} R) AddCommGrpCat.{u + 1}) ≅
      sheafCompose J (forget₂ (ModuleCat.{u + 1} S) AddCommGrpCat.{u + 1}) := Iso.refl _

abbrev restrictForgetIso
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {T U : Sheaf J RingCat.{u + 1}} (a : T ⟶ U) :
    SheafOfModules.restrictScalars a ⋙ SheafOfModules.toSheaf T ≅
      SheafOfModules.toSheaf U := Iso.refl _

abbrev normalized
    {C C' D D' E : Type*} [Category C] [Category C'] [Category D] [Category D'] [Category E]
    {Q : C ⥤ C'} {R : D ⥤ D'} {F : C ⥤ D} {F' : C' ⥤ D'}
    {H : D ⥤ E} {H' : D' ⥤ E} {G : C ⥤ E} {G' : C' ⥤ E}
    (c : Q ⋙ F' ≅ F ⋙ R) (r : R ⋙ H' ≅ H)
    (a : F ⋙ H ≅ G) (a' : F' ⋙ H' ≅ G') (q : Q ⋙ G' ≅ G) : Prop :=
  (Functor.isoWhiskerRight c H' ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F r ≪≫ a).hom =
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft Q a' ≪≫ q).hom

theorem normalized_of_app
    {C C' D D' E : Type*} [Category C] [Category C'] [Category D] [Category D'] [Category E]
    {Q : C ⥤ C'} {R : D ⥤ D'} {F : C ⥤ D} {F' : C' ⥤ D'}
    {H : D ⥤ E} {H' : D' ⥤ E} {G : C ⥤ E} {G' : C' ⥤ E}
    (c : Q ⋙ F' ≅ F ⋙ R) (r : R ⋙ H' ≅ H)
    (a : F ⋙ H ≅ G) (a' : F' ⋙ H' ≅ G') (q : Q ⋙ G' ≅ G)
    (h : ∀ X, H'.map (c.hom.app X) ≫ r.hom.app (F.obj X) ≫ a.hom.app X =
      a'.hom.app (Q.obj X) ≫ q.hom.app X) :
    normalized c r a a' q := by
  unfold normalized
  apply NatTrans.ext
  funext X
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, Category.comp_id,
    Category.assoc] using h X

end AlgebraicGeometry.Scheme.CoefficientSheafificationSquare
