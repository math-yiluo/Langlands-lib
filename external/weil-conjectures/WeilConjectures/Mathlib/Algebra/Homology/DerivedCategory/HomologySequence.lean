/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Vanishing in the derived category is detected by homology

An object of the derived category of an abelian category is zero if and only if all of its
homology objects are zero (`DerivedCategory.isZero_iff`). This is the object-level
counterpart of `DerivedCategory.isIso_iff`.
-/

@[expose] public section

universe w v u

open CategoryTheory Limits ZeroObject

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- An object of the derived category is zero if and only if all its homology objects are
zero. -/
lemma isZero_iff (K : DerivedCategory C) :
    IsZero K ↔ ∀ n : ℤ, IsZero ((homologyFunctor C n).obj K) := by
  refine ⟨fun hK n ↦ (homologyFunctor C n).map_isZero hK, fun hK ↦ ?_⟩
  -- The morphism `K ⟶ 0` induces isomorphisms between zero objects on all homology objects.
  have : IsIso (0 : K ⟶ 0) := by
    rw [isIso_iff]
    exact fun n ↦ isIso_of_source_target_iso_zero _ ((hK n).isoZero)
      (((homologyFunctor C n).map_isZero (isZero_zero _)).isoZero)
  exact (isZero_zero _).of_iso (asIso (0 : K ⟶ 0))

/-- An object of the derived category all of whose homology objects vanish is zero. -/
lemma isZero_of_forall_isZero_homology (K : DerivedCategory C)
    (hK : ∀ n : ℤ, IsZero ((homologyFunctor C n).obj K)) : IsZero K :=
  (isZero_iff K).2 hK

end DerivedCategory
