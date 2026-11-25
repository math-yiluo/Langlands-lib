/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.NatIso

/-!
# Recognising components of inverses of natural isomorphisms

- `CategoryTheory.Iso.eq_inv_app_of_comp_hom_app_eq_id`: a left inverse of a component of a
  natural isomorphism is the component of its inverse.
- `CategoryTheory.comp_comp_eq_comp_of_comp_eq`: the cancellation `a ≫ b ≫ c' = a ≫ a'` for
  `a ≫ b = c` and right inverses `c'`, `a'` of `c`, `a`.
-/

@[expose] public section

namespace CategoryTheory

/-- A left inverse of a component of a natural isomorphism is the component of the inverse. -/
lemma Iso.eq_inv_app_of_comp_hom_app_eq_id {C D : Type*} [Category* C] [Category* D]
    {F G : C ⥤ D} (α : F ≅ G) (X : C) {g : G.obj X ⟶ F.obj X} (h : g ≫ α.hom.app X = 𝟙 _) :
    g = α.inv.app X := by
  rw [← cancel_mono (α.hom.app X), h, Iso.inv_hom_id_app]

/-- If `a ≫ b = c`, and `c'`, `a'` are right inverses of `c` and `a`, then
`a ≫ b ≫ c' = a ≫ a'`. -/
lemma comp_comp_eq_comp_of_comp_eq {𝒜 : Type*} [Category* 𝒜] {X Y Z : 𝒜} (a : X ⟶ Y)
    (a' : Y ⟶ X) (b : Y ⟶ Z) (c : X ⟶ Z) (c' : Z ⟶ X) (hb : a ≫ b = c) (hc : c ≫ c' = 𝟙 X)
    (ha : a ≫ a' = 𝟙 X) : a ≫ b ≫ c' = a ≫ a' := by
  rw [← Category.assoc, hb, hc, ha]

end CategoryTheory
