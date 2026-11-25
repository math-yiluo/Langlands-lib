/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! # Vanishing of the other summands after applying cohomology

Source: latest blueprint lemma-integral-linear-character--2, isotypic
splitting and the assertion that only the constant summand remains on constants.
-/

@[expose] public section
set_option autoImplicit false

universe v₁ v₂ u₁ u₂ w
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- A zero-preserving functor kills the other summands if the total object is zero
or one summand inclusion becomes an isomorphism.
Source: blueprint lemma-integral-linear-character--2, isotypic decomposition
and constants paragraph (blueprint: lem-fd-cohomology-character-coproduct-glue).

Proof: use the coproduct property to project onto the selected summand, with
identity on that summand and zero on all others. If the total object becomes
zero, this projection becomes zero. If another inclusion becomes invertible,
its zero composite with the projection again forces the latter to become zero.
The image of the selected summand's identity is the composite of its inclusion
and this zero projection, so the selected summand has zero identity. -/
theorem isZero_coproduct_summand_of_total_or_other_iso
    {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C]
    {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {J : Type w} (M : J → C) (P : C) (ι : ∀ j, M j ⟶ P)
    (hc : IsColimit (Cofan.mk P ι)) (i j : J) (hij : i ≠ j)
    (h : IsZero (F.obj P) ∨ IsIso (F.map (ι i))) : IsZero (F.obj (M j)) := by
  classical
  let c : Cofan M := Cofan.mk (M j) (fun k ↦
    if h : k = j then eqToHom (congrArg M h) else 0)
  let r : P ⟶ M j := hc.desc c
  have hrj : ι j ≫ r = 𝟙 (M j) := by
    simpa [r, c] using hc.fac c (Discrete.mk j)
  have hri : ι i ≫ r = 0 := by
    simpa [r, c, hij] using hc.fac c (Discrete.mk i)
  have hz : F.map r = 0 := by
    rcases h with h | h
    · exact h.eq_of_src _ _
    · let := h
      apply (cancel_epi (F.map (ι i))).1
      rw [← F.map_comp, hri, F.map_zero, comp_zero]
  apply (IsZero.iff_id_eq_zero _).2
  calc
    𝟙 (F.obj (M j)) = F.map (𝟙 (M j)) := (F.map_id _).symm
    _ = F.map (ι j ≫ r) := congrArg F.map hrj.symm
    _ = F.map (ι j) ≫ F.map r := F.map_comp _ _
    _ = 0 := by rw [hz, comp_zero]

end CategoryTheory
