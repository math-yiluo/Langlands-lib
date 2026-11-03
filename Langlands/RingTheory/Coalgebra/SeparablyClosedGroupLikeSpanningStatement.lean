import Mathlib.FieldTheory.IsSepClosed
import Mathlib.RingTheory.Coalgebra.GroupLike
import Mathlib.RingTheory.Coalgebra.TensorProduct

/-!
# Descent of group-like spanning over a separably closed field

This module states a pure-coalgebra consequence of the coetale argument in
Milne, Algebraic Groups (2017), Theorem 12.18(c) ⇒ (d). The additional descent
steps and the exact scope of the statement are explained in the paired Markdown.
-/

universe u v w

open scoped TensorProduct

namespace Langlands.CoalgebraDescent

/-- If a scalar extension of a coalgebra over a separably closed field is spanned
by its group-like elements, then the original coalgebra is also so spanned. -/
def SeparablyClosedGroupLikeSpanningStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsSepClosed k]
    (C : Type v) [AddCommGroup C] [Module k C] [Coalgebra k C]
    (K : Type w) [Field K] [Algebra k K],
    Submodule.span K {x : K ⊗[k] C | IsGroupLikeElem K x} = ⊤ →
      Submodule.span k {x : C | IsGroupLikeElem k x} = ⊤

end Langlands.CoalgebraDescent
