/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The scalar unit determined by a sections comparison

Source: the Yoneda calculation underlying Stacks 03CZ and 08JA.
-/

@[expose] public section
set_option autoImplicit false

universe a av b bv g
open CategoryTheory
namespace CategoryTheory

/-- A natural sections comparison is determined by its value at the identity of
the object representing target sections. This formulation records that value as
an explicit morphism, rather than choosing a witness of an existence theorem.
Source: Yoneda, applied to the global-sections comparison of Stacks 03CZ and 08JA.
(blueprint: lem-coef-represented-sections-scalar-unit).

Proof: put r equal to the target representation of the transported section.
Naturality of the target representation identifies its image of the identity
section with the transported section. Naturality of the inverse sections
comparison pulls this equality back to source sections. Naturality of the source
representation then identifies the composite of the recorded unit with U(r)
with the source representation of the original section. -/
theorem representedSections_scalar_unit
    {A : Type a} [Category.{av} A] {B : Type b} [Category.{bv} B]
    (U : B ⥤ A) (ΓA : A ⥤ AddCommGrpCat.{g}) (ΓB : B ⥤ AddCommGrpCat.{g})
    (σ : U ⋙ ΓA ≅ ΓB) (IA : A) (IB : B)
    (α : ∀ X, ΓA.obj X ≃ (IA ⟶ X)) (β : ∀ X, ΓB.obj X ≃ (IB ⟶ X))
    (hα : ∀ {X Y} (f : X ⟶ Y) (x : ΓA.obj X),
      α Y (ΓA.map f x) = α X x ≫ f)
    (hβ : ∀ {X Y} (f : X ⟶ Y) (x : ΓB.obj X),
      β Y (ΓB.map f x) = β X x ≫ f)
    (X : B) (y : ΓA.obj (U.obj X)) :
    α (U.obj IB) (σ.inv.app IB ((β IB).symm (𝟙 IB))) ≫
        U.map (β X (σ.hom.app X y)) = α (U.obj X) y := by
  let c := (β IB).symm (𝟙 IB)
  let r := β X (σ.hom.app X y)
  have hb : ΓB.map r c = σ.hom.app X y := by
    apply (β X).injective
    rw [hβ]
    simp only [c, Equiv.apply_symm_apply, Category.id_comp, r]
  have hs := congrArg (fun f ↦ f c) (σ.inv.naturality r).symm
  change ΓA.map (U.map r) (σ.inv.app IB c) =
    σ.inv.app X (ΓB.map r c) at hs
  have ha := hα (U.map r) (σ.inv.app IB c)
  rw [hs, hb] at ha
  have hi : σ.inv.app X (σ.hom.app X y) = y := by
    exact congrArg (fun f ↦ f y) (σ.hom_inv_id_app X)
  rw [hi] at ha
  exact ha.symm

end CategoryTheory
