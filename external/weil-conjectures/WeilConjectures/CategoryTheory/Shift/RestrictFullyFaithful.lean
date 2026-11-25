/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Mathlib.CategoryTheory.Shift.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Shift.CommShift

/-!
# Restricted adjunctions and preimages of isomorphisms commuting with shifts

* `CategoryTheory.NatTrans.CommShift.preimageIso_whiskeringRight`: the preimage along whiskering
  with a fully faithful functor commuting with shifts of an isomorphism commuting with shifts
  commutes with shifts.
* `CategoryTheory.NatTrans.CommShift.eqToHom_congrArg`: `eqToHom` between members of a family of
  functors commuting with shifts commutes with shifts.
* `CategoryTheory.Adjunction.commShift_ofNatIsoRight`: transporting an adjunction commuting with
  shifts along an isomorphism of right adjoints commuting with shifts.
* `CategoryTheory.Adjunction.commShift_restrictFullyFaithful`: the restriction of an adjunction
  commuting with shifts along fully faithful functors commuting with shifts.
-/

@[expose] public section

namespace CategoryTheory

open Category

variable {A : Type*} [AddMonoid A]

namespace NatTrans.CommShift

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [HasShift C A] [HasShift D A] [HasShift E A]

/-- The preimage, along whiskering with a fully faithful functor commuting with shifts, of an
isomorphism commuting with shifts commutes with shifts. -/
instance preimageIso_whiskeringRight {F₁ F₂ : C ⥤ D} [F₁.CommShift A] [F₂.CommShift A]
    {G : D ⥤ E} (hG : G.FullyFaithful) [G.CommShift A] (e : F₁ ⋙ G ≅ F₂ ⋙ G)
    [NatTrans.CommShift e.hom A] :
    NatTrans.CommShift ((hG.whiskeringRight C).preimageIso e).hom A := by
  have := hG.faithful
  have : NatTrans.CommShift (Functor.whiskerRight ((hG.whiskeringRight C).preimageIso e).hom G)
      A := by
    have h : Functor.whiskerRight ((hG.whiskeringRight C).preimageIso e).hom G = e.hom :=
      (hG.whiskeringRight C).map_preimage e.hom
    rw [h]
    infer_instance
  exact of_whiskerRight _ G

/-- `eqToHom` between two members of a family of functors commuting with shifts commutes with
shifts. -/
lemma eqToHom_congrArg {α : Sort*} (F : α → C ⥤ D) [∀ a, (F a).CommShift A] {a b : α}
    (h : a = b) : NatTrans.CommShift (eqToHom (congrArg F h)) A := by
  subst h
  rw [eqToHom_refl]
  infer_instance

section Iso

variable {F G H : C ⥤ D} [F.CommShift A] [G.CommShift A] [H.CommShift A]

instance trans_hom (e : F ≅ G) (e' : G ≅ H) [NatTrans.CommShift e.hom A]
    [NatTrans.CommShift e'.hom A] : NatTrans.CommShift (e ≪≫ e').hom A := by
  rw [Iso.trans_hom]
  infer_instance

instance isoWhiskerLeft_hom (K : E ⥤ C) [K.CommShift A] (e : F ≅ G)
    [NatTrans.CommShift e.hom A] : NatTrans.CommShift (Functor.isoWhiskerLeft K e).hom A := by
  rw [Functor.isoWhiskerLeft_hom]
  infer_instance

instance isoWhiskerRight_hom (K : D ⥤ E) [K.CommShift A] (e : F ≅ G)
    [NatTrans.CommShift e.hom A] : NatTrans.CommShift (Functor.isoWhiskerRight e K).hom A := by
  rw [Functor.isoWhiskerRight_hom]
  infer_instance

instance inv (τ : F ⟶ G) [IsIso τ] [NatTrans.CommShift τ A] :
    NatTrans.CommShift (CategoryTheory.inv τ) A :=
  of_isIso τ A

instance asIso_hom (τ : F ⟶ G) [IsIso τ] [NatTrans.CommShift τ A] :
    NatTrans.CommShift (asIso τ).hom A := by
  rw [CategoryTheory.asIso_hom]
  infer_instance

end Iso

end NatTrans.CommShift

section Conjugate

variable {C D : Type*} [Category* C] [Category* D] [HasShift C A] [HasShift D A]
  {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)

/-- The inverse conjugate of `α : R₁ ⟶ R₂` is `L₂ ⟶ L₂ R₁ L₁ ⟶ L₂ R₂ L₁ ⟶ L₁`. -/
lemma conjugateEquiv_symm_eq (α : R₁ ⟶ R₂) :
    (conjugateEquiv adj₁ adj₂).symm α =
      L₂.leftUnitor.inv ≫ Functor.whiskerRight adj₁.unit L₂ ≫ (Functor.associator L₁ R₁ L₂).hom ≫
        Functor.whiskerLeft L₁ (Functor.whiskerRight α L₂) ≫
        Functor.whiskerLeft L₁ adj₂.counit ≫ L₁.rightUnitor.hom := by
  ext X
  have h := conjugateEquiv_counit_symm adj₁ adj₂ α (L₁.obj X)
  have hn := ((conjugateEquiv adj₁ adj₂).symm α).naturality (adj₁.unit.app X)
  simp only [Functor.id_obj, Functor.comp_obj, NatTrans.comp_app, Functor.leftUnitor_inv_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.rightUnitor_hom_app, Category.id_comp, Category.comp_id]
  simp only [Functor.comp_obj, Functor.id_obj] at hn
  rw [h, reassoc_of% hn, adj₁.left_triangle_components, Category.comp_id]

variable [L₁.CommShift A] [L₂.CommShift A] [R₁.CommShift A] [R₂.CommShift A]
  [adj₁.CommShift A] [adj₂.CommShift A]

/-- The inverse conjugate of a natural transformation commuting with shifts, with respect to
adjunctions commuting with shifts, commutes with shifts. -/
instance NatTrans.CommShift.conjugateEquiv_symm (α : R₁ ⟶ R₂) [NatTrans.CommShift α A] :
    NatTrans.CommShift ((CategoryTheory.conjugateEquiv adj₁ adj₂).symm α) A := by
  rw [conjugateEquiv_symm_eq]
  infer_instance

instance NatTrans.CommShift.conjugateIsoEquiv_hom (α : L₂ ≅ L₁) [NatTrans.CommShift α.hom A] :
    NatTrans.CommShift (conjugateIsoEquiv adj₁ adj₂ α).hom A :=
  inferInstanceAs (NatTrans.CommShift (CategoryTheory.conjugateEquiv adj₁ adj₂ α.hom) A)

instance NatTrans.CommShift.conjugateIsoEquiv_symm_hom (β : R₁ ≅ R₂)
    [NatTrans.CommShift β.hom A] :
    NatTrans.CommShift ((conjugateIsoEquiv adj₁ adj₂).symm β).hom A :=
  inferInstanceAs (NatTrans.CommShift ((CategoryTheory.conjugateEquiv adj₁ adj₂).symm β.hom) A)

end Conjugate

namespace Adjunction

section OfNatIsoRight

variable {C D : Type*} [Category* C] [Category* D] [HasShift C A] [HasShift D A]
  {F : C ⥤ D} {H H' : D ⥤ C} [F.CommShift A] [H.CommShift A] [H'.CommShift A]

/-- An adjunction commuting with shifts, transported along an isomorphism of right adjoints
commuting with shifts, commutes with shifts. -/
lemma commShift_ofNatIsoRight (adj : F ⊣ H) (iso : H ≅ H') [adj.CommShift A]
    [NatTrans.CommShift iso.hom A] : (adj.ofNatIsoRight iso).CommShift A where
  commShift_unit := by dsimp only [ofNatIsoRight]; infer_instance
  commShift_counit := by dsimp only [ofNatIsoRight]; infer_instance

end OfNatIsoRight

section Restrict

variable {C C' D D' : Type*} [Category* C] [Category* C'] [Category* D] [Category* D']
  [HasShift C A] [HasShift C' A] [HasShift D A] [HasShift D' A]
  {iC : C ⥤ C'} {iD : D ⥤ D'} {L' : C' ⥤ D'} {R' : D' ⥤ C'} {L : C ⥤ D} {R : D ⥤ C}
  [iC.CommShift A] [iD.CommShift A] [L'.CommShift A] [R'.CommShift A] [L.CommShift A]
  [R.CommShift A]

/-- The restriction of an adjunction commuting with shifts along fully faithful functors
commuting with shifts, through comparison isomorphisms commuting with shifts, commutes with
shifts. -/
lemma commShift_restrictFullyFaithful (adj : L' ⊣ R') (hiC : iC.FullyFaithful)
    (hiD : iD.FullyFaithful) (comm1 : iC ⋙ L' ≅ L ⋙ iD) (comm2 : iD ⋙ R' ≅ R ⋙ iC)
    [adj.CommShift A] [NatTrans.CommShift comm1.hom A] [NatTrans.CommShift comm2.hom A] :
    (adj.restrictFullyFaithful hiC hiD comm1 comm2).CommShift A := by
  have := hiC.faithful
  have e : Functor.whiskerRight (adj.restrictFullyFaithful hiC hiD comm1 comm2).unit iC =
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv ≫
        Functor.whiskerLeft iC adj.unit ≫ (Functor.associator _ _ _).inv ≫
        Functor.whiskerRight comm1.hom R' ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft L comm2.hom ≫ (Functor.associator _ _ _).inv := by
    ext X
    simp
  have : NatTrans.CommShift
      (Functor.whiskerRight (adj.restrictFullyFaithful hiC hiD comm1 comm2).unit iC) A := by
    rw [e]
    infer_instance
  exact .mk' _ _ (NatTrans.CommShift.of_whiskerRight _ iC)

end Restrict

end Adjunction

end CategoryTheory
