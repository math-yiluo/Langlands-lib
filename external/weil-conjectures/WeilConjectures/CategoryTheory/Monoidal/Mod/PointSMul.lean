/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.CommMon_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod

/-!
# Multiplication by a point of a commutative monoid on its modules

Let `A` be a commutative monoid object of a braided monoidal category `C` and `φ : 𝟙_ C ⟶ A` a
point of `A` (for a sheaf of rings, a global section). The multiplication by `φ`,
`M ≅ 𝟙 ⊗ M ⟶ A ⊗ M ⟶ M`, is `A`-linear, hence a natural endomorphism of the identity functor of
the category of `A`-modules (`CategoryTheory.Mod.pointSMul`).

A lax monoidal functor `G`, turning `B`-modules into `A`-modules along a monoid morphism
`ι : A ⟶ G B`, intertwines the multiplications by points `φ` of `A` and `φ'` of `B` as soon as
`φ ≫ ι = ε ≫ G φ'` (`CategoryTheory.Mod.map_pointSMulHom`).
-/

@[expose] public section

universe v₁ v₂ u₁ u₂

open CategoryTheory MonoidalCategory MonObj Functor.LaxMonoidal

namespace CategoryTheory.Mod

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

section Hom

variable {A : C} [MonObj A] (φ : 𝟙_ C ⟶ A)

/-- The multiplication `X ≅ 𝟙 ⊗ X ⟶ A ⊗ X ⟶ X` by a point `φ : 𝟙_ C ⟶ A` on an `A`-module. -/
def pointSMulHom (X : C) [ModObj A X] : X ⟶ X :=
  (λ_ X).inv ≫ φ ▷ X ≫ act X

lemma pointSMulHom_naturality {M N : Mod C A} (f : M ⟶ N) :
    f.hom ≫ pointSMulHom φ N.X = pointSMulHom φ M.X ≫ f.hom := by
  simp only [pointSMulHom, Category.assoc, act_hom, leftUnitor_inv_naturality_assoc,
    whisker_exchange_assoc]

end Hom

section Comm

variable [BraidedCategory C] {A : C} [MonObj A] [IsCommMonObj A] (φ : 𝟙_ C ⟶ A)

lemma leftUnitor_inv_whiskerRight_mul :
    (λ_ A).inv ≫ φ ▷ A ≫ μ[A] = (ρ_ A).inv ≫ A ◁ φ ≫ μ[A] := by
  conv_rhs => rw [← IsCommMonObj.mul_comm A, BraidedCategory.braiding_naturality_right_assoc,
    rightUnitor_inv_braiding_assoc]

lemma act_comp_pointSMulHom (X : C) [ModObj A X] :
    act X ≫ pointSMulHom φ X = A ◁ pointSMulHom φ X ≫ act X := by
  have h₁ : act X ≫ pointSMulHom φ X =
      ((λ_ A).inv ≫ φ ▷ A ≫ μ[A]) ▷ X ≫ act X := by
    simp only [pointSMulHom, leftUnitor_inv_naturality_assoc, comp_whiskerRight, Category.assoc,
      mul_act, leftUnitor_inv_whiskerRight]
    rw [whisker_exchange_assoc, whiskerRight_tensor]
    simp only [Category.assoc]
  have h₂ : A ◁ pointSMulHom φ X ≫ act X =
      ((ρ_ A).inv ≫ A ◁ φ ≫ μ[A]) ▷ X ≫ act X := by
    simp only [pointSMulHom, MonoidalCategory.whiskerLeft_comp, Category.assoc, comp_whiskerRight,
      mul_act]
    rw [associator_naturality_middle_assoc, triangle_assoc_comp_right_inv_assoc]
  rw [h₁, h₂, leftUnitor_inv_whiskerRight_mul]

/-- **Multiplication by a point of a commutative monoid**, as a natural endomorphism of the
identity functor of the category of modules. -/
def pointSMul : 𝟭 (Mod C A) ⟶ 𝟭 (Mod C A) where
  app M := homMk (pointSMulHom φ M.X) (act_comp_pointSMulHom φ M.X)
  naturality _ _ f := Mod.hom_ext _ _ (pointSMulHom_naturality φ f)

lemma pointSMul_app_hom (M : Mod C A) : ((pointSMul φ).app M).hom = pointSMulHom φ M.X :=
  rfl

end Comm

section Functor

open scoped Obj

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] (G : D ⥤ C) [G.LaxMonoidal]
  {A : C} [MonObj A] {B : D} [MonObj B] (ι : A ⟶ G.obj B) [IsMonHom ι]
  {φ : 𝟙_ C ⟶ A} {φ' : 𝟙_ D ⟶ B} (hφ : φ ≫ ι = ε G ≫ G.map φ')

include hφ in
/-- A lax monoidal functor `G`, turning `B`-modules into `A`-modules along `ι : A ⟶ G B`,
carries the multiplication by `φ'` to the multiplication by `φ` when `φ ≫ ι = ε ≫ G φ'`. -/
lemma map_pointSMulHom (N : Mod D B) :
    pointSMulHom φ ((comap ι).obj ((G.mapMod B).obj N)).X = G.map (pointSMulHom φ' N.X) := by
  change (λ_ (G.obj N.X)).inv ≫ φ ▷ G.obj N.X ≫ ι ▷ G.obj N.X ≫ Functor.LaxMonoidal.μ G B N.X ≫
    G.map (act N.X) = _
  rw [← comp_whiskerRight_assoc, hφ, comp_whiskerRight_assoc, μ_natural_left_assoc,
    left_unitality_inv_assoc, pointSMulHom, G.map_comp, G.map_comp]

end Functor

end CategoryTheory.Mod
