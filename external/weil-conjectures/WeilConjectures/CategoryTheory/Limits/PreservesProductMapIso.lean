/-
Copyright (c) 2026 Anthropic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Products of isomorphisms into the image of a product

Given isomorphisms `e j : g j ≅ G.obj (f j)` and a functor `G` preserving the product of `f`,
the isomorphism `∏ᶜ g ≅ G.obj (∏ᶜ f)` obtained from `Pi.mapIso e` and `PreservesProduct.iso`
is computed after composition with the images of the projections
(`CategoryTheory.Limits.PreservesProduct.mapIso_trans_iso_symm_hom_map_π`).
-/

@[expose] public section

namespace CategoryTheory.Limits.PreservesProduct

/-- The isomorphism `∏ᶜ g ≅ G.obj (∏ᶜ f)` induced by componentwise isomorphisms
`g j ≅ G.obj (f j)`, followed by the image of a projection, is the projection followed by
the component. -/
@[reassoc]
theorem mapIso_trans_iso_symm_hom_map_π {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {J : Type*} {f : J → C} {g : J → D} [HasProduct f] [HasProductsOfShape J D]
    [PreservesLimit (Discrete.functor f) G] (e : ∀ j, g j ≅ G.obj (f j)) (j : J) :
    (Pi.mapIso e ≪≫ (PreservesProduct.iso G f).symm).hom ≫ G.map (Pi.π f j) =
      Pi.π g j ≫ (e j).hom := by
  rw [← piComparison_comp_π G f j]
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← PreservesProduct.iso_hom,
    Iso.inv_hom_id_assoc]
  exact Pi.mapIso_hom_π e j

end CategoryTheory.Limits.PreservesProduct
