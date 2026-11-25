/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Sites.SheafComposeMonoidal

/-!
# The lax monoidal structure of `sheafCompose` on underlying presheaves

For a lax monoidal functor `G : A ⥤ B`, the postcomposition `sheafCompose J G` of sheaves is lax
monoidal (`CategoryTheory.sheafComposeLaxMonoidal`). This file records that its unit and
multiplication, read on the underlying presheaves, are the objectwise unit and multiplication of
`G`: the comparison `sheafToPresheafCompWhiskeringRightIsoSheafCompose` between the two ways of
computing the underlying presheaf of `G ∘ P` is the identity
(`CategoryTheory.Sheaf.sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app`), and it is a
monoidal natural isomorphism.

## Main results

- `CategoryTheory.Sheaf.ε_sheafToPresheaf_comp_map_ε_sheafCompose` and
  `CategoryTheory.Sheaf.μ_sheafToPresheaf_comp_map_μ_sheafCompose`.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits Opposite Functor.LaxMonoidal

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] (J : GrothendieckTopology C)
  {A : Type*} [Category A] [MonoidalCategory A] [BraidedCategory A]
  {B : Type*} [Category B] [MonoidalCategory B] [BraidedCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A]
  [(J.W (A := B)).IsMonoidal] [HasWeakSheafify J B]
  (G : A ⥤ B) [J.HasSheafCompose G] [G.LaxMonoidal]

attribute [local instance] Sheaf.monoidalCategory

omit [MonoidalCategory A] [BraidedCategory A] [MonoidalCategory B] [BraidedCategory B]
  [(J.W (A := A)).IsMonoidal] [HasWeakSheafify J A] [(J.W (A := B)).IsMonoidal] [G.LaxMonoidal] in
/-- The comparison between the underlying presheaf of `sheafCompose J G P` and the
postcomposition `P ⋙ G` is the identity: it is the unit of sheafification followed by the
inverse of the counit, which compose to the identity on a sheaf. -/
lemma sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app (P : Sheaf J A) :
    (sheafToPresheafCompWhiskeringRightIsoSheafCompose J G).hom.app P = 𝟙 _ := by
  simp [sheafToPresheafCompWhiskeringRightIsoSheafCompose,
    sheafToPresheafCompWhiskeringRightCompPresheafToSheafIso]
  rfl

omit [BraidedCategory A] [BraidedCategory B] in
/-- The unit of `sheafCompose J G`, read on the underlying presheaves, is the objectwise unit
of `G`. -/
lemma ε_sheafToPresheaf_comp_map_ε_sheafCompose :
    ε (sheafToPresheaf J B) ≫ (sheafToPresheaf J B).map (ε (sheafCompose J G)) =
      ε ((Functor.whiskeringRight Cᵒᵖ A B).obj G) ≫
        ((Functor.whiskeringRight Cᵒᵖ A B).obj G).map (ε (sheafToPresheaf J A)) := by
  have h := NatTrans.IsMonoidal.unit
    (τ := (sheafToPresheafCompWhiskeringRightIsoSheafCompose J G).hom)
  rw [sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app, Category.comp_id] at h
  simpa only [Functor.LaxMonoidal.comp_ε] using h.symm

omit [BraidedCategory A] [BraidedCategory B] in
/-- The multiplication of `sheafCompose J G`, read on the underlying presheaves, is the
objectwise multiplication of `G`. -/
lemma μ_sheafToPresheaf_comp_map_μ_sheafCompose (P Q : Sheaf J A) :
    «μ» (sheafToPresheaf J B) _ _ ≫ (sheafToPresheaf J B).map («μ» (sheafCompose J G) P Q) =
      «μ» ((Functor.whiskeringRight Cᵒᵖ A B).obj G) _ _ ≫
        ((Functor.whiskeringRight Cᵒᵖ A B).obj G).map («μ» (sheafToPresheaf J A) P Q) := by
  have h := NatTrans.IsMonoidal.tensor
    (τ := (sheafToPresheafCompWhiskeringRightIsoSheafCompose J G).hom) P Q
  simp only [sheafToPresheafCompWhiskeringRightIsoSheafCompose_hom_app, Category.comp_id,
    MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp] at h
  simpa only [Functor.LaxMonoidal.comp_μ] using h.symm

end CategoryTheory.Sheaf
