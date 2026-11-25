/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Adjunction.Additive

/-!
# Additive hom equivalences of an adjunction up to isomorphism

For an adjunction `F ⊣ G` between preadditive categories with `F` additive, and isomorphisms
`F.obj A ≅ A'` and `G.obj B ≅ B'`, the additive equivalence `Adjunction.homAddEquiv` transports
to an additive equivalence `(A' ⟶ B) ≃+ (A ⟶ B')`.
-/

@[expose] public section

universe u₁ u₂ v₁ v₂

namespace CategoryTheory

namespace Adjunction

open Category

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D] [Preadditive C]
  [Preadditive D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.Additive]

/-- The additive equivalence `(A' ⟶ B) ≃+ (A ⟶ B')` induced by an adjunction `F ⊣ G` with `F`
additive and isomorphisms `F.obj A ≅ A'` and `G.obj B ≅ B'`. -/
def homAddEquivOfIso {A : C} {A' B : D} {B' : C} (i₁ : F.obj A ≅ A') (i₂ : G.obj B ≅ B') :
    (A' ⟶ B) ≃+ (A ⟶ B') where
  toFun f := adj.homEquiv _ _ (i₁.hom ≫ f) ≫ i₂.hom
  invFun g := i₁.inv ≫ (adj.homEquiv _ _).symm (g ≫ i₂.inv)
  left_inv f := by simp
  right_inv g := by simp
  map_add' a b := by simp [Preadditive.comp_add, Preadditive.add_comp]

lemma homAddEquivOfIso_apply {A : C} {A' B : D} {B' : C} (i₁ : F.obj A ≅ A')
    (i₂ : G.obj B ≅ B') (f : A' ⟶ B) :
    adj.homAddEquivOfIso i₁ i₂ f = adj.homEquiv _ _ (i₁.hom ≫ f) ≫ i₂.hom :=
  rfl

/-- Naturality of `Adjunction.homAddEquivOfIso` in the target. -/
lemma homAddEquivOfIso_comp {A : C} {A' B B₂ : D} {B' B₂' : C} (i₁ : F.obj A ≅ A')
    (i₂ : G.obj B ≅ B') (i₂' : G.obj B₂ ≅ B₂') (g : B ⟶ B₂) (g' : B' ⟶ B₂')
    (hg : G.map g ≫ i₂'.hom = i₂.hom ≫ g') (f : A' ⟶ B) :
    adj.homAddEquivOfIso i₁ i₂' (f ≫ g) = adj.homAddEquivOfIso i₁ i₂ f ≫ g' := by
  simp only [homAddEquivOfIso_apply, ← assoc, homEquiv_naturality_right]
  simp only [assoc, hg]

end Adjunction

end CategoryTheory
