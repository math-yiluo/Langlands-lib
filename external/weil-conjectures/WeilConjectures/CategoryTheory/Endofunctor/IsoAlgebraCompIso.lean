/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebraComp

/-!
# Composites of transported functors of algebras

For commutation isomorphisms `e₁ : L₁ ⋙ G ≅ F ⋙ L₁`, `e₂ : L₂ ⋙ H ≅ G ⋙ L₂` and
`e₃ : L₃ ⋙ H ≅ F ⋙ L₃`, an isomorphism `β : L₃ ≅ L₁ ⋙ L₂` compatible with them induces an
isomorphism `mapOfNatIso e₁ ⋙ mapOfNatIso e₂ ≅ mapOfNatIso e₃`
(`CategoryTheory.Endofunctor.IsoAlgebra.mapOfNatIsoCompIsoOfIso`) whose components are those
of `β⁻¹` on the underlying objects.
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {C D E : Type*} [Category C] [Category D] [Category E] {F : C ⥤ C} {G : D ⥤ D}
  {H : E ⥤ E} {L₁ : C ⥤ D} {L₂ : D ⥤ E} {L₃ : C ⥤ E} {e₁ : L₁ ⋙ G ≅ F ⋙ L₁}
  {e₂ : L₂ ⋙ H ≅ G ⋙ L₂} {e₃ : L₃ ⋙ H ≅ F ⋙ L₃}

/-- An isomorphism `β : L₃ ≅ L₁ ⋙ L₂` compatible with the commutation isomorphisms induces an
isomorphism `mapOfNatIso e₁ ⋙ mapOfNatIso e₂ ≅ mapOfNatIso e₃`. -/
noncomputable def mapOfNatIsoCompIsoOfIso (β : L₃ ≅ L₁ ⋙ L₂)
    (hβ : Functor.whiskerRight β.hom H ≫ (compCommIso e₁ e₂).hom =
      e₃.hom ≫ Functor.whiskerLeft F β.hom) :
    mapOfNatIso e₁ ⋙ mapOfNatIso e₂ ≅ mapOfNatIso e₃ :=
  NatIso.ofComponents (fun K ↦ ObjectProperty.isoMk _ (Algebra.isoMk (β.symm.app K.carrier) (by
      have h := congr_app hβ K.carrier
      simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
        compCommIso_hom_app] at h
      change H.map (β.inv.app K.carrier) ≫ e₃.hom.app K.carrier ≫ L₃.map K.str.hom =
        (e₂.hom.app (L₁.obj K.carrier) ≫ L₂.map (e₁.hom.app K.carrier ≫ L₁.map K.str.hom)) ≫
          β.inv.app K.carrier
      rw [← cancel_epi (H.map (β.hom.app K.carrier)), ← Functor.map_comp_assoc,
        Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp,
        Category.assoc]
      simp only [Category.assoc] at h ⊢
      rw [reassoc_of% h]
      have n := β.hom.naturality K.str.hom
      simp only [Functor.comp_map] at n
      rw [reassoc_of% n.symm]
      simp)))
    (fun f ↦ ObjectProperty.hom_ext _ (Algebra.Hom.ext (β.inv.naturality f.hom.f)))

@[simp]
lemma mapOfNatIsoCompIsoOfIso_hom_app_hom_f (β : L₃ ≅ L₁ ⋙ L₂)
    (hβ : Functor.whiskerRight β.hom H ≫ (compCommIso e₁ e₂).hom =
      e₃.hom ≫ Functor.whiskerLeft F β.hom) (K : IsoAlgebra F) :
    ((mapOfNatIsoCompIsoOfIso β hβ).hom.app K).hom.f = β.inv.app K.carrier :=
  rfl

end CategoryTheory.Endofunctor.IsoAlgebra
