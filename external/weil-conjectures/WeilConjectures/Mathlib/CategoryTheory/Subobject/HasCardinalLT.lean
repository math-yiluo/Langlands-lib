/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Subobject.HasCardinalLT
public import WeilConjectures.Mathlib.CategoryTheory.Abelian.Subobject

/-!
# Cardinality of the lattice of subobjects and epimorphisms

`Mathlib/CategoryTheory/Subobject/HasCardinalLT.lean` shows that a bound on the cardinality
of the subobjects of `Y` gives the same bound for the subobjects of `X` when there is a
monomorphism `X ⟶ Y`. Here we prove the dual statement for an epimorphism `X ⟶ Y`, in an
abelian category.

## Main results

* `CategoryTheory.Subobject.hasCardinalLT_of_epi`

-/

@[expose] public section

universe w v u

namespace CategoryTheory.Subobject

open Limits

variable {C : Type u} [Category.{v} C] [Abelian C]

lemma hasCardinalLT_of_epi {X : C} {κ : Cardinal.{w}}
    (h : HasCardinalLT (Subobject X) κ) {Y : C} (p : X ⟶ Y) [Epi p] :
    HasCardinalLT (Subobject Y) κ :=
  h.of_injective (Subobject.pullback p).obj (fun T₁ T₂ e ↦ by
    rw [← exists_obj_pullback_obj p T₁, ← exists_obj_pullback_obj p T₂, e])

end CategoryTheory.Subobject
