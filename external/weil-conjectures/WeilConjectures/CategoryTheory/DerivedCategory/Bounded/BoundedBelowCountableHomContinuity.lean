/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.DirectSum.Basic

/-!
# Countable Hom continuity on bounded-below families

Source: Bhatt–Scholze, The pro-étale topology for schemes, Lemma 6.8.12 and
Proposition 6.8.14(2) (blueprint: def-weil-pbc-countable-bounded-below-hom-continuity).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open CategoryTheory CategoryTheory.Limits DirectSum

namespace DerivedCategory

/-- Hom from K commutes with every countable coproduct of a family with a common
cohomological lower bound, after every integer shift. The definition quantifies
all coproduct cofans, avoiding a choice of coproduct. Their shifted legs define
exactly the canonical comparison. No bound on K itself is imposed.
Source: Bhatt–Scholze, Lemma 6.8.12, used in Proposition 6.8.14(2)
(blueprint: def-weil-pbc-countable-bounded-below-hom-continuity). -/
def CountableBoundedBelowHomContinuous {A : Type u} [Category.{v} A] [Abelian A]
    [HasDerivedCategory.{w} A] (K : DerivedCategory A) : Prop :=
  ∀ (L : ℕ → DerivedCategory A) (b : ℤ), (∀ n : ℕ, (L n).IsGE b) →
    ∀ (B : DerivedCategory A) (ι : ∀ n : ℕ, L n ⟶ B), IsColimit (Cofan.mk B ι) →
      ∀ q : ℤ, Function.Bijective
        (DirectSum.toAddMonoid (fun n : ℕ ↦ Preadditive.rightComp K ((ι n)⟦q⟧')) :
          (⨁ n : ℕ, (K ⟶ (L n)⟦q⟧)) →+ (K ⟶ B⟦q⟧))

end DerivedCategory
