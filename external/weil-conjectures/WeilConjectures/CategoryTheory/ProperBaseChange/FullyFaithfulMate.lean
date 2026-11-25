/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.EssentialImage
import Mathlib.CategoryTheory.Yoneda

/-! # Mates between fully faithful embeddings -/

@[expose] public section

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory

open Category

/-- A mate between fully faithful embeddings is invertible when its target stays in the image.
Source: the Hom-set proof of restriction of adjunctions, Mathlib
`Adjunction.restrictFullyFaithful` (blueprint: lem-weil-pbc-fully-faithful-mate-image).

Proof. Fix an object d and write the mate's target as G(t). By full faithfulness of G,
the mate is G(f) for a morphism f : R₁(d) ⟶ t. Postcomposition with f on Hom(X, R₁(d))
is the composite of the first adjunction, full faithfulness of H, precomposition with
the given left isomorphism, the second adjunction, the target identification and full
faithfulness of G. Hence this Hom map is bijective for every X. Yoneda shows f is an
isomorphism, and G(f), and therefore the mate component, are isomorphisms. -/
theorem isIso_mateEquiv_of_fullyFaithful_of_essImage
    {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C}
    {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    (hG : G.FullyFaithful) (hH : H.FullyFaithful)
    (α : G ⋙ L₂ ≅ L₁ ⋙ H)
    (himage : ∀ d, G.essImage (R₂.obj (H.obj d))) :
    IsIso (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom)) := by
  suffices ∀ d, IsIso
      ((mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom)).app d) by
    exact @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ this
  intro d
  obtain ⟨t, ⟨e⟩⟩ := himage d
  let β := (mateEquiv adj₁ adj₂ (TwoSquare.mk _ _ _ _ α.hom))
  let f : R₁.obj d ⟶ t := hG.preimage (β.app d ≫ e.inv)
  have hf : IsIso f := by
    apply isIso_of_yoneda_map_bijective
    intro X
    let φ : (X ⟶ R₁.obj d) ≃ (X ⟶ t) :=
      (adj₁.homEquiv X d).symm.trans (hH.homEquiv.trans
        ((Iso.homCongr (α.app X).symm (Iso.refl _)).trans
          ((adj₂.homEquiv (G.obj X) (H.obj d)).trans
            ((Iso.homCongr (Iso.refl _) e.symm).trans hG.homEquiv.symm))))
    convert φ.bijective using 1
    funext k
    apply hG.map_injective
    dsimp [φ, f]
    simp only [Functor.FullyFaithful.map_preimage, Functor.map_comp]
    simp only [mateEquiv_apply, ← assoc, NatTrans.comp_app, Functor.comp_obj, Functor.id_obj,
      Functor.rightUnitor_inv_app, Functor.whiskerLeft_app, id_comp,
      Functor.associator_hom_app, comp_id, Functor.associator_inv_app,
      Functor.whiskerRight_app, Functor.comp_map, Functor.leftUnitor_hom_app,
      Adjunction.homEquiv_counit, Functor.FullyFaithful.homEquiv_apply, Functor.map_comp,
      Iso.homCongr_apply, Iso.symm_inv, Iso.app_hom, Iso.refl_hom, Adjunction.homEquiv_unit,
      Iso.refl_inv, Iso.symm_hom, Functor.FullyFaithful.homEquiv_symm_apply,
      Functor.FullyFaithful.map_preimage, Iso.cancel_iso_inv_right, β]
    change ((G.map k ≫ adj₂.unit.app (G.obj (R₁.obj d))) ≫
        R₂.map (α.hom.app (R₁.obj d))) ≫ R₂.map (H.map (adj₁.counit.app d)) = _
    rw [← adj₂.unit_naturality]
    simp only [Category.assoc, ← R₂.map_comp]
    rw [← Functor.comp_map G L₂, α.hom.naturality_assoc k]
    simp only [Functor.comp_map]
  have : IsIso (G.map f) := by
    let := hG.full
    let := hG.faithful
    infer_instance
  rw [show G.map f = β.app d ≫ e.inv from hG.map_preimage _] at this
  exact IsIso.of_isIso_comp_right (β.app d) e.inv

end CategoryTheory
