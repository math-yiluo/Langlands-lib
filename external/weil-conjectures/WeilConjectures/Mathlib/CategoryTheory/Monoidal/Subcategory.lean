/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Subcategory

/-!
# Restrictions of monoidal functors to full monoidal subcategories

Let `P` and `Q` be monoidal properties of objects of monoidal categories `C` and `D`, and
`F : C ⥤ D` a strong monoidal functor sending objects satisfying `P` to objects satisfying `Q`.
The restriction `Q.lift (P.ι ⋙ F) hF : P.FullSubcategory ⥤ Q.FullSubcategory` is then strong
monoidal, with the comparison isomorphisms of `F`. The file also records the underlying
morphisms of the tensor comparisons of such a restriction, and of tensor products of morphisms,
whiskerings, associators and braidings in a full monoidal subcategory.

## Main definitions

- `CategoryTheory.ObjectProperty.monoidalLift`: the strong monoidal structure on the
  restriction of a strong monoidal functor to full monoidal subcategories.
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.ObjectProperty

open MonoidalCategory Functor.LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
  {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {P : ObjectProperty C} [P.IsMonoidal] {Q : ObjectProperty D} [Q.IsMonoidal]
  (F : C ⥤ D) [F.Monoidal] (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))

/-- The restriction `Q.lift (P.ι ⋙ F)` of a strong monoidal functor `F` to full monoidal
subcategories is strong monoidal, with the comparison isomorphisms of `F`. -/
noncomputable instance monoidalLift : (Q.lift (P.ι ⋙ F) hF).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { εIso := Q.fullyFaithfulι.preimageIso (Functor.Monoidal.εIso F)
      μIso X Y := Q.fullyFaithfulι.preimageIso (Functor.Monoidal.μIso F X.obj Y.obj)
      μIso_hom_natural_left f X' := hom_ext _ (μ_natural_left F f.hom X'.obj)
      μIso_hom_natural_right X' f := hom_ext _ (μ_natural_right F X'.obj f.hom)
      associativity X Y Z := hom_ext _ (associativity F X.obj Y.obj Z.obj)
      left_unitality X := hom_ext _ (left_unitality F X.obj)
      right_unitality X := hom_ext _ (right_unitality F X.obj) }

/-- The underlying morphism of the tensor comparison `δ` of the restriction `monoidalLift` of a
strong monoidal functor is the tensor comparison of the functor. -/
lemma monoidalLift_δ_hom (X Y : P.FullSubcategory) :
    (Functor.OplaxMonoidal.δ (Q.lift (P.ι ⋙ F) hF) X Y).hom =
      Functor.OplaxMonoidal.δ F X.obj Y.obj :=
  rfl

end CategoryTheory.ObjectProperty

namespace CategoryTheory.ObjectProperty

open MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] (P : ObjectProperty C) [P.IsMonoidal]

/-- The underlying morphism of a left whiskering in a full monoidal subcategory. -/
lemma whiskerLeft_hom (X : P.FullSubcategory) {Y Z : P.FullSubcategory} (f : Y ⟶ Z) :
    (X ◁ f).hom = X.obj ◁ f.hom :=
  rfl

/-- The underlying morphism of a right whiskering in a full monoidal subcategory. -/
lemma whiskerRight_hom {X Y : P.FullSubcategory} (f : X ⟶ Y) (Z : P.FullSubcategory) :
    (f ▷ Z).hom = f.hom ▷ Z.obj :=
  rfl

/-- The underlying morphism of the associator in a full monoidal subcategory. -/
lemma associator_hom_hom (X Y Z : P.FullSubcategory) :
    (α_ X Y Z).hom.hom = (α_ X.obj Y.obj Z.obj).hom :=
  rfl

/-- The underlying morphism of the inverse associator in a full monoidal subcategory. -/
lemma associator_inv_hom (X Y Z : P.FullSubcategory) :
    (α_ X Y Z).inv.hom = (α_ X.obj Y.obj Z.obj).inv :=
  rfl

variable {P} in
/-- The underlying morphism of a tensor product of morphisms in a full monoidal subcategory. -/
lemma tensorHom_hom' {A B A' B' : P.FullSubcategory} (a : A ⟶ A') (b : B ⟶ B') :
    (a ⊗ₘ b).hom = a.hom ⊗ₘ b.hom :=
  rfl

variable {P} in
/-- The underlying morphism of the braiding of a full braided subcategory is the braiding. -/
lemma fullBraidedSubcategory_braiding_hom_hom [BraidedCategory C] (X Y : P.FullSubcategory) :
    (@BraidedCategory.braiding _ _ _ (fullBraidedSubcategory P) X Y).hom.hom =
      (β_ X.obj Y.obj).hom :=
  rfl

end CategoryTheory.ObjectProperty
