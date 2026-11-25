/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.AbelianImages

/-!
# Images under conjugation and exact functors

In an abelian category, endomorphisms conjugate under an isomorphism have isomorphic images
(`CategoryTheory.nonempty_iso_image_of_comp_eq`), and an exact functor of abelian categories
preserves images (`CategoryTheory.nonempty_iso_obj_image`).
-/

@[expose] public section

open CategoryTheory Limits

namespace CategoryTheory

/-- The images of two endomorphisms conjugate under an isomorphism are isomorphic. -/
theorem nonempty_iso_image_of_comp_eq {C : Type*} [Category* C]
    [Abelian C] {A B : C} (e : A ≅ B) (f : A ⟶ A) (g : B ⟶ B) [HasImage f] [HasImage g]
    (h : f ≫ e.hom = e.hom ≫ g) :
    Nonempty (Limits.image f ≅ Limits.image g) := by
  have hg : (e.inv ≫ Limits.factorThruImage f) ≫ (Limits.image.ι f ≫ e.hom) = g := by
    rw [Category.assoc, Limits.image.fac_assoc, h, Iso.inv_hom_id_assoc]
  have : StrongEpi (e.inv ≫ Limits.factorThruImage f) := strongEpi_of_epi _
  exact ⟨Limits.image.isoStrongEpiMono _ _ hg⟩

/-- An exact functor of abelian categories preserves images. -/
theorem nonempty_iso_obj_image {C D : Type*} [Category* C] [Category* D]
    [Abelian C] [Abelian D] (Φ : C ⥤ D) [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
    {A B : C} (f : A ⟶ B) [HasImage f] [HasImage (Φ.map f)] :
    Nonempty (Φ.obj (image f) ≅ image (Φ.map f)) :=
  ⟨Φ.mapIso (Abelian.imageIsoImage _).symm ≪≫ Abelian.PreservesImage.iso Φ _ ≪≫
    Abelian.imageIsoImage _⟩

end CategoryTheory
