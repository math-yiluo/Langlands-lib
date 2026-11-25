/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.Algebra.GroupWithZero.Units.Basic

/-! # Transport of invertible integral scalar endomorphisms

Source: canonical q^(-d) normalization of proposition-compatibility-purity-change-coefficients.
-/

@[expose] public section
set_option autoImplicit false
universe u₁ u₂ v₁ v₂
open CategoryTheory
namespace CategoryTheory

/-- The ring inverse of an invertible endomorphism is its categorical inverse.
Source: inverse scalar convention in coefficient-change normalization
(blueprint: lem-pur-coefficient-inverse-scalar).
Proof: its product with the endomorphism is the identity by the unit inverse law;
cancel that endomorphism against the categorical inverse. -/
theorem ringInverse_eq_categoricalInv
    {C : Type u₁} [Category.{v₁} C] [Preadditive C] {X : C} (f : End X) [IsIso (f).asHom] :
    Ring.inverse f = .of (inv (f).asHom) := by
  apply End.ext
  apply (cancel_mono f.asHom).1
  have h := Ring.mul_inverse_cancel f ((isUnit_iff_isIso f).mpr inferInstance)
  have h' : (Ring.inverse (M₀ := End X) f).asHom ≫ f.asHom = 𝟙 X := by
    simpa only [End.mul_asHom, End.one_asHom] using congr($(h).asHom)
  exact h'.trans (IsIso.inv_hom_id f.asHom).symm

/-- Every arrow intertwines an invertible natural-number scalar and its inverse.
Source: canonical q^(-d) normalization in coefficient change
(blueprint: lem-pur-coefficient-inverse-scalar).
Proof: additive functors preserve natural-number multiples of identities. Such
multiples commute with every morphism. Cancel the target scalar; the two inverse
identities reduce the desired equation to that scalar commutation equation. -/
theorem map_inverse_nsmul_id_natural
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    [Preadditive C] [Preadditive D] (F : C ⥤ D) [F.Additive]
    (n : ℕ) (X : C) (Y : D) (e : F.obj X ⟶ Y)
    [IsIso (n • 𝟙 X)] [IsIso (n • 𝟙 Y)] :
    F.map ((Ring.inverse (M₀ := End X) (n • (1 : End X)))).asHom ≫ e =
      e ≫ (Ring.inverse (M₀ := End Y) (n • (1 : End Y))).asHom := by
  have : IsIso (n • (1 : End X)).asHom := ‹IsIso (n • 𝟙 X)›
  have : IsIso (n • (1 : End Y)).asHom := ‹IsIso (n • 𝟙 Y)›
  rw [ringInverse_eq_categoricalInv, ringInverse_eq_categoricalInv, F.map_inv]
  simp only [End.nsmul_asHom, End.one_asHom]
  have hs : F.map (n • 𝟙 X) ≫ e = e ≫ (n • 𝟙 Y) := by
    simp only [F.map_nsmul, F.map_id, Preadditive.nsmul_comp,
      Preadditive.comp_nsmul, Category.id_comp, Category.comp_id]
  apply (cancel_mono (n • 𝟙 Y)).1
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← hs, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end CategoryTheory
