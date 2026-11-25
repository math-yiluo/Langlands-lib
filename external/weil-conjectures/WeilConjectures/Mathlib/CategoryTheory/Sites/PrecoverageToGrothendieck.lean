/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck

/-!
# Composition of covering presieves for `GrothendieckTopology.toPrecoverage`
-/

@[expose] public section

namespace CategoryTheory

/-- Composition of covering presieves along `Presieve.bind` is covering for a Grothendieck
topology viewed as a precoverage. -/
theorem GrothendieckTopology.toPrecoverage_bind_mem {C : Type*}
    [Category* C] (T : GrothendieckTopology C) {X : C} (R : Presieve X)
    (P : ∀ ⦃Y : C⦄ (f : Y ⟶ X), R f → Presieve Y) (hR : R ∈ T.toPrecoverage X)
    (hP : ∀ (Y : C) (f : Y ⟶ X) (hf : R f), P f hf ∈ T.toPrecoverage Y) :
    R.bind (fun _ _ hf ↦ P _ hf) ∈ T.toPrecoverage X := by
  rw [GrothendieckTopology.mem_toPrecoverage_iff] at hR ⊢
  refine T.transitive hR _ ?_
  rintro Z g ⟨W, h, f, hf, rfl⟩
  rw [Sieve.pullback_comp]
  refine T.pullback_stable h (T.superset_covering ?_ (hP _ f hf))
  rintro V k ⟨V', l, m, hm, rfl⟩
  exact ⟨V', l, m ≫ f, ⟨_, _, _, hf, hm, rfl⟩, by simp⟩

end CategoryTheory
