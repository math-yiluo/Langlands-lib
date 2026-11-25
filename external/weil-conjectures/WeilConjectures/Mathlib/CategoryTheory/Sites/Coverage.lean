/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck

/-!
# Grothendieck

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.Sites.Grothendieck`).
-/

@[expose] public section

namespace CategoryTheory

lemma GrothendieckTopology.transitive_of_presieve {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {X : C} (R : Presieve X) (hR : Sieve.generate R ∈ J X)
    (S : Sieve X) (h : ∀ ⦃Y : C⦄ (g : Y ⟶ X), R g → S.pullback g ∈ J Y) :
    S ∈ J X := by
  refine J.transitive hR _ ?_
  rintro Y f ⟨W, g, v, hv, rfl⟩
  rw [Sieve.pullback_comp]
  exact J.pullback_stable _ (h _ hv)

end CategoryTheory
