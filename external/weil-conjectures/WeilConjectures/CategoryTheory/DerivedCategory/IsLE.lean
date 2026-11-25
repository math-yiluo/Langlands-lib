/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Retract

/-!
# Vanishing above a degree in a derived category

Two closure properties of the objects of `D(C)` vanishing above a degree `n`: they are stable
under isomorphisms (`DerivedCategory.isLE_of_iso_of_isLE`, the hypothesis being passed
explicitly rather than as an instance) and under retracts (`DerivedCategory.isLE_of_retract`).
-/

@[expose] public section

open CategoryTheory Limits

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- An object isomorphic to an object vanishing above `n` vanishes above `n`; the hypothesis is
explicit, so that it can be given for an object which is only definitionally equal to the source
of `e`. -/
lemma isLE_of_iso_of_isLE {X Y : DerivedCategory C} (e : X ≅ Y) {n : ℤ} (h : X.IsLE n) :
    Y.IsLE n :=
  TStructure.t.isLE_of_iso e n

/-- A retract of an object vanishing above `n` vanishes above `n`. -/
lemma isLE_of_retract {X Y : DerivedCategory C} (e : Retract X Y) (n : ℤ) [Y.IsLE n] :
    X.IsLE n :=
  (isLE_iff X n).2 fun q hq ↦ by
    let F := homologyFunctor C q
    have : IsSplitMono (F.map e.i) :=
      IsSplitMono.mk' ⟨F.map e.r, by rw [← F.map_comp, e.retract, F.map_id]⟩
    exact IsZero.of_mono (F.map e.i) (((isLE_iff Y n).1 inferInstance) q hq)

end DerivedCategory
