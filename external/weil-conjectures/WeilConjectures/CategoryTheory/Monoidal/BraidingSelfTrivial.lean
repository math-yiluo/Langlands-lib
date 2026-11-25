/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Shift.CommShiftTwo

/-!
# Objects with trivial self-braiding

An object `X` of a braided monoidal category has *trivial self-braiding* if
`(β_ X X).hom = 𝟙 (X ⊗ X)`. This file records the elementary stability properties of this
condition:

* it is invariant under isomorphism (`CategoryTheory.MonoidalCategory.braiding_self_eq_id_of_iso`)
  and holds for the unit (`CategoryTheory.MonoidalCategory.braiding_tensorUnit_self`);
* for a braided functor `F`, `X` has trivial self-braiding after applying `F` if and only if
  `F` kills `β_ X X - 𝟙` (`CategoryTheory.Functor.braiding_obj_self_eq_id_iff`);
* for a symmetric braiding compatible with shifts by `ℤ` in the Koszul way, it is stable under
  even shifts (`CategoryTheory.MonoidalCategory.braiding_shift_self_eq_id`): the braiding of
  `X⟦n⟧ ⊗ X⟦n⟧` is the shift of the braiding of `X ⊗ X` up to the sign `(-1) ^ (n * n)`.
-/

@[expose] public section

open CategoryTheory Category MonoidalCategory Functor.LaxMonoidal

namespace CategoryTheory

namespace MonoidalCategory

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

/-- Trivial self-braiding is invariant under isomorphism. -/
lemma braiding_self_eq_id_of_iso {X Y : C} (e : X ≅ Y) (h : (β_ Y Y).hom = 𝟙 _) :
    (β_ X X).hom = 𝟙 _ := by
  rw [← cancel_mono (e.hom ⊗ₘ e.hom), ← BraidedCategory.braiding_naturality, h, comp_id, id_comp]

/-- The unit has trivial self-braiding. -/
lemma braiding_tensorUnit_self : (β_ (𝟙_ C) (𝟙_ C)).hom = 𝟙 _ := by
  simp only [braiding_tensorUnit_left]
  rw [unitors_equal, Iso.hom_inv_id]

/-- An object isomorphic to the unit has trivial self-braiding. -/
lemma braiding_self_eq_id_of_iso_tensorUnit {X : C} (e : X ≅ 𝟙_ C) : (β_ X X).hom = 𝟙 _ :=
  braiding_self_eq_id_of_iso e braiding_tensorUnit_self

end MonoidalCategory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalCategory D] [BraidedCategory D] (F : C ⥤ D) [F.Braided]

/-- For a braided functor `F`, the image `F X` has trivial self-braiding if and only if `F` maps
the self-braiding of `X` to the identity. -/
lemma braiding_obj_self_eq_id_iff (X : C) :
    (β_ (F.obj X) (F.obj X)).hom = 𝟙 _ ↔ F.map (β_ X X).hom = 𝟙 _ := by
  have h := LaxBraided.braided (F := F) X X
  refine ⟨fun h' ↦ ?_, fun h' ↦ ?_⟩
  · rw [← cancel_epi (μ F X X), h, h', id_comp, comp_id]
  · rw [← cancel_mono (μ F X X), ← h, h', comp_id, id_comp]

/-- A braided functor preserves trivial self-braidings. -/
lemma braiding_obj_self_eq_id {X : C} (hX : (β_ X X).hom = 𝟙 _) :
    (β_ (F.obj X) (F.obj X)).hom = 𝟙 _ := by
  rw [braiding_obj_self_eq_id_iff, hX, F.map_id]

end Functor

namespace MonoidalCategory

variable {D : Type*} [Category* D] [Preadditive D] [MonoidalCategory D] [BraidedCategory D]
  [HasShift D ℤ] [∀ n : ℤ, (shiftFunctor D n).Additive] [(curriedTensor D).CommShift₂Int]

/-- **Even shifts preserve trivial self-braidings.** Let `D` be a braided monoidal category
whose tensor product commutes with the shifts by `ℤ` with the Koszul signs, whose braiding is
symmetric and commutes with the shifts in the second variable. If `X` has trivial
self-braiding, so does `X⟦n⟧` for every even `n`: the braiding of `X⟦n⟧ ⊗ X⟦n⟧` is the shift by
`n + n` of the braiding of `X ⊗ X` with the sign `(-1) ^ (n * n)`. -/
lemma braiding_shift_self_eq_id
    (hB : ∀ (X Y : D) (n : ℤ), (β_ X (Y⟦n⟧)).hom ≫
        (((curriedTensor D).flip.obj X).commShiftIso n).hom.app Y =
      (((curriedTensor D).obj X).commShiftIso n).hom.app Y ≫ ((β_ X Y).hom)⟦n⟧')
    (hS : ∀ X Y : D, (β_ X Y).hom ≫ (β_ Y X).hom = 𝟙 _)
    {X : D} (hX : (β_ X X).hom = 𝟙 _) {n : ℤ} (hn : Even n) :
    (β_ (X⟦n⟧) (X⟦n⟧)).hom = 𝟙 _ := by
  -- the braiding of `X⟦n⟧ ⊗ X` moves the shift from the first to the second factor
  have h₁ : (β_ (X⟦n⟧) X).hom ≫ (((curriedTensor D).obj X).commShiftIso n).hom.app X =
      (((curriedTensor D).flip.obj X).commShiftIso n).hom.app X := by
    rw [← cancel_epi (β_ X (X⟦n⟧)).hom, ← assoc, hS, id_comp, hB, hX]
    erw [CategoryTheory.Functor.map_id]
    exact (comp_id _).symm
  have hε (Z : D) : ((CommShift₂Setup.int (D := D)).ε n n).val.app Z = 𝟙 Z := by
    rw [CommShift₂Setup.int_ε, (hn.mul_right n).neg_one_zpow]
    rfl
  have h₂ := (curriedTensor D).commShift₂_comm (h := .int) X X n n
  simp only [shiftComm, shiftFunctorComm_eq_refl, hε] at h₂
  rw [← cancel_mono ((((curriedTensor D).flip.obj (X⟦n⟧)).commShiftIso n).hom.app X), hB,
    id_comp, ← cancel_mono ((shiftFunctor D n).map
      ((((curriedTensor D).obj X).commShiftIso n).hom.app X)),
    assoc, ← Functor.map_comp, h₁]
  simpa using h₂

end MonoidalCategory

end CategoryTheory
