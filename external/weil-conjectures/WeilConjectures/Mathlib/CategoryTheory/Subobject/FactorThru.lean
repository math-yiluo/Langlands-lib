/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.FactorThru
public import WeilConjectures.Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Factorisation criteria for inequalities between subobjects

The order on `Subobject X` is characterised by the relation `Subobject.Factors`: a subobject
`mk i` is contained in `T` exactly when `i` factors through `T`. We record this, together with
the corresponding descriptions of `Subobject.pullback` and of the image pushforward
`Subobject.«exists»`, and deduce that image pushforward is functorial in the morphism.

## Main results

- `CategoryTheory.Subobject.mk_le_iff_factors`
- `CategoryTheory.Subobject.factors_pullback_obj_iff`
- `CategoryTheory.Subobject.exists_le_iff`
- `CategoryTheory.Subobject.exists_obj_comp`
- `CategoryTheory.Subobject.map_obj_le_map_obj_iff`
-/

@[expose] public section

universe v u

namespace CategoryTheory.Subobject

open Limits

variable {C : Type u} [Category.{v} C] {X Y Z : C}

/-- A subobject `mk i` is contained in `T` exactly when `i` factors through `T`. -/
theorem mk_le_iff_factors {A : C} (i : A ⟶ X) [Mono i] (T : Subobject X) :
    mk i ≤ T ↔ T.Factors i :=
  ⟨fun h => factors_of_le i h (mk_factors_self i),
    fun h => mk_le_of_comm (T.factorThru i h) (factorThru_arrow _ _ _)⟩

/-- The order on subobjects is characterised by factorisations of the arrows. -/
theorem le_iff_factors_arrow (S T : Subobject X) : S ≤ T ↔ T.Factors S.arrow := by
  conv_lhs => rw [← mk_arrow S]
  exact mk_le_iff_factors _ _

@[simp]
theorem map_obj_eq_mk (f : X ⟶ Y) [Mono f] (S : Subobject X) :
    (map f).obj S = mk (S.arrow ≫ f) := by
  conv_lhs => rw [← mk_arrow S]
  exact map_mk _ _

section Pullback

variable [HasPullbacks C]

/-- A morphism `h` factors through the pullback of `T` along `f` exactly when `h ≫ f`
factors through `T`. -/
theorem factors_pullback_obj_iff (f : X ⟶ Y) (T : Subobject Y) {A : C} (h : A ⟶ X) :
    ((pullback f).obj T).Factors h ↔ T.Factors (h ≫ f) := by
  constructor
  · intro hf
    rw [← factorThru_arrow _ _ hf, Category.assoc, ← (isPullback f T).w]
    exact factors_of_factors_right _ (factors_comp_arrow _)
  · intro hf
    refine (factors_iff _ _).2 ?_
    exact ⟨(isPullback f T).lift (T.factorThru _ hf) h (by simp), (isPullback f T).lift_snd _ _ _⟩

theorem map_obj_le_map_obj_iff (f : X ⟶ Y) [Mono f] (S T : Subobject X) :
    (map f).obj S ≤ (map f).obj T ↔ S ≤ T := by
  refine ⟨fun h => ?_, fun h => (map f).monotone h⟩
  simpa only [pullback_map_self] using (pullback f).monotone h

end Pullback

section Exists

variable [HasImages C]

/-- The image of `S` under `f` is contained in `T` exactly when `S.arrow ≫ f` factors
through `T`. -/
theorem exists_le_iff (f : X ⟶ Y) (S : Subobject X) (T : Subobject Y) :
    («exists» f).obj S ≤ T ↔ T.Factors (S.arrow ≫ f) := by
  constructor
  · intro h
    refine factors_of_le _ h ?_
    rw [← (imageFactorisation f S).F.fac]
    exact factors_comp_arrow _
  · intro h
    exact le_of_comm ((imageFactorisation f S).isImage.lift
      { I := (T : C), m := T.arrow, e := T.factorThru _ h })
      ((imageFactorisation f S).isImage.lift_fac _)

variable [HasPullbacks C]

/-- Image pushforward is functorial in the morphism. -/
theorem exists_obj_comp (f : X ⟶ Y) (g : Y ⟶ Z) (S : Subobject X) :
    («exists» g).obj ((«exists» f).obj S) = («exists» (f ≫ g)).obj S := by
  have key : ∀ T : Subobject Z, («exists» g).obj ((«exists» f).obj S) ≤ T ↔
      («exists» (f ≫ g)).obj S ≤ T := fun T => by
    rw [exists_le_iff (f ≫ g) S T, ← Category.assoc]
    exact (gc_exists_pullback g _ T).trans
      ((exists_le_iff f S _).trans (factors_pullback_obj_iff g T _))
  exact le_antisymm ((key _).2 le_rfl) ((key _).1 le_rfl)

end Exists

end CategoryTheory.Subobject
