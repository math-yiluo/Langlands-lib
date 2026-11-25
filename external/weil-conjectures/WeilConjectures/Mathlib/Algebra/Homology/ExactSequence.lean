/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Exact functors preserve exact sequences of length two

An exact functor between abelian categories sends an exact sequence `X₀ ⟶ X₁ ⟶ X₂` to an exact
sequence.
-/

@[expose] public section

namespace CategoryTheory.ComposableArrows

open Limits

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]

/-- An exact functor sends an exact sequence `X₀ ⟶ X₁ ⟶ X₂` to an exact sequence. -/
lemma Exact.map_mk₂ {X₀ X₁ X₂ : C} {f : X₀ ⟶ X₁} {g : X₁ ⟶ X₂} (h : (mk₂ f g).Exact)
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (mk₂ (F.map f) (F.map g)).Exact := by
  have w : f ≫ g = 0 := h.toIsComplex.zero 0
  have hS : (ShortComplex.mk f g w).Exact := (exact₂_iff _ h.toIsComplex).1 h
  exact (hS.map F).exact_toComposableArrows

end CategoryTheory.ComposableArrows
