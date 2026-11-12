import Langlands.GroupScheme.Reductive.AbsolutelyAlmostSimple
import Mathlib.FieldTheory.IsSepClosed

/-! # Almost-simplicity over a separably closed field is absolute -/

universe u

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Corollary 24.2: every almost-simple group over a separably
closed field is absolutely almost-simple. This is a statement only. -/
def SeparablyClosedAlmostSimpleAbsoluteStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsSepClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsAlmostSimple G → IsAbsolutelyAlmostSimple G

end Langlands.GroupScheme
