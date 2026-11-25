/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.Preadditive
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Conv

/-!
# Global sections acting on module objects

For a monoid object `R` of a preadditive monoidal category `C` and an `R`-module object `M`, a
global section `s : 𝟙 ⟶ R` acts on the underlying object `M.X` by
`M.X ≅ 𝟙 ⊗ M.X ⟶ R ⊗ M.X ⟶ M.X`. This is a ring homomorphism
`CategoryTheory.Mod.sectionActRingHom M : Γ R →+* End M.X`, natural in `M`
(`CategoryTheory.Mod.sectionActRingHom_comp_hom`).
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Preadditive

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {R : C} [MonObj R]

/-- The action of a morphism `s : 𝟙 ⟶ R` on an `R`-module object `X`. -/
def sectionAct (X : C) [ModObj R X] (s : 𝟙_ C ⟶ R) : X ⟶ X :=
  (λ_ X).inv ≫ s ▷ X ≫ act X

lemma sectionAct_one (X : C) [ModObj R X] : sectionAct X η[R] = 𝟙 X := by
  simp [sectionAct]

lemma sectionAct_mul (X : C) [ModObj R X] (s t : Γ R) :
    sectionAct X (s * t).hom = sectionAct X t.hom ≫ sectionAct X s.hom := by
  have h : (λ_ X).inv ≫ (λ_ (𝟙_ C)).inv ▷ X ≫ (s.hom ⊗ₘ t.hom) ▷ X ≫ (α_ R R X).hom =
      (λ_ X).inv ≫ (λ_ (𝟙_ C ⊗ X)).inv ≫ s.hom ▷ (𝟙_ C ⊗ X) ≫ R ◁ t.hom ▷ X := by
    have h₀ : (λ_ X).inv ≫ (λ_ (𝟙_ C)).inv ▷ X ≫ (α_ (𝟙_ C) (𝟙_ C) X).hom =
        (λ_ X).inv ≫ (λ_ (𝟙_ C ⊗ X)).inv := by
      monoidal
    rw [tensorHom_def, comp_whiskerRight, Category.assoc, associator_naturality_middle,
      associator_naturality_left_assoc, reassoc_of% h₀]
  simp only [sectionAct, Γ.mul_hom, comp_whiskerRight, Category.assoc, mul_act]
  rw [reassoc_of% h, ← whisker_exchange_assoc s.hom (t.hom ▷ X),
    ← leftUnitor_inv_naturality_assoc (t.hom ▷ X), leftUnitor_inv_naturality_assoc (act X),
    whisker_exchange_assoc s.hom (act X)]

lemma sectionAct_comp {X Y : C} [ModObj R X] [ModObj R Y] (f : X ⟶ Y) [IsModHom R f]
    (s : 𝟙_ C ⟶ R) : sectionAct X s ≫ f = f ≫ sectionAct Y s := by
  simp only [sectionAct, Category.assoc, act_comp, ← whisker_exchange_assoc,
    leftUnitor_inv_naturality_assoc]

variable [Preadditive C] [MonoidalPreadditive C]

/-- The action of the global sections `Γ R` of a monoid object `R` on the underlying object of
an `R`-module object `M`: a global section `s` acts by `M.X ≅ 𝟙 ⊗ M.X ⟶ R ⊗ M.X ⟶ M.X`. -/
def sectionActRingHom (M : Mod C R) : Γ R →+* End M.X where
  toFun s := .of (sectionAct M.X s.hom)
  map_one' := by rw [Γ.one_hom, sectionAct_one]; rfl
  map_mul' s t := End.ext (sectionAct_mul M.X s t)
  map_zero' := End.ext (by simp [sectionAct])
  map_add' s t := End.ext (by simp [sectionAct])

lemma sectionActRingHom_apply (M : Mod C R) (s : Γ R) :
    sectionActRingHom M s = .of ((λ_ M.X).inv ≫ s.hom ▷ M.X ≫ act M.X) :=
  rfl

/-- The action of global sections commutes with morphisms of `R`-modules. -/
@[reassoc]
lemma sectionActRingHom_comp_hom {M N : Mod C R} (f : M ⟶ N) (s : Γ R) :
    (sectionActRingHom M s).asHom ≫ f.hom = f.hom ≫ (sectionActRingHom N s).asHom :=
  sectionAct_comp f.hom s.hom

end CategoryTheory.Mod
