import Langlands.CategoryTheory.Renard.CompositionChains
import Mathlib.Order.Cover

/-!
# Simple cokernels and covers of subobjects

This is a derived internal prerequisite for Renard 2026, Appendix A.VI.2(9)
and A.VI.3, printed page 263 / PDF page 269. The source does not separately
state this criterion. This module defines a proposition and supplies no proof.
-/

namespace Langlands.Renard

open CategoryTheory CategoryTheory.Limits

universe u v

/-- The actual quotient `B/A` is simple precisely when `B` covers `A` in the
order of subobjects. This is an internal categorical bridge, stated only. -/
def SubobjectSimpleCokernelStatement (C : Type u) [Category.{v} C] [Abelian C] : Prop :=
  ∀ (X : C) (A B : Subobject X) (h : A ≤ B),
    Simple (cokernel (Subobject.ofLE A B h)) ↔ A ⋖ B

end Langlands.Renard
