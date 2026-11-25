/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import Mathlib.CategoryTheory.Subobject.WellPowered

/-!
# Essential smallness from monomorphisms into a small family

In a well-powered category, a property of objects is essentially small as soon as every object
satisfying it is a subobject of a member of a small family of objects: the subobjects of the
members of the family form a small set.
-/

@[expose] public section

universe w v u

namespace CategoryTheory.ObjectProperty

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C] [WellPowered.{w} C]

/-- In a well-powered category, a property of objects is essentially small if each object
satisfying it admits a monomorphism into a member of a family of objects indexed by a small
type. -/
lemma EssentiallySmall.of_forall_exists_mono (P : ObjectProperty C) {ι : Type w} (T : ι → C)
    (h : ∀ X, P X → ∃ (i : ι) (f : X ⟶ T i), Mono f) :
    ObjectProperty.EssentiallySmall.{w} P := by
  refine ⟨ObjectProperty.ofObj (fun x : Σ i, Shrink.{w} (Subobject (T i)) ↦
    Subobject.underlying.obj ((equivShrink (Subobject (T x.1))).symm x.2)), inferInstance,
    fun X hX ↦ ?_⟩
  obtain ⟨i, f, hf⟩ := h X hX
  refine ⟨_, ObjectProperty.ofObj_apply _ ⟨i, equivShrink _ (Subobject.mk f)⟩, ⟨?_⟩⟩
  exact (Subobject.underlyingIso f).symm ≪≫ eqToIso (by rw [Equiv.symm_apply_apply])

end CategoryTheory.ObjectProperty
