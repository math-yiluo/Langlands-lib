import Langlands.GroupScheme.PseudoComplete
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # Descent of the DVR lifting property along algebraic field extensions

This proposition states the descent of the valuative half of pseudo-completeness,
`PseudoComplete.HasDVRLifting`, from the base change along an algebraic field extension.
This module defines the proposition and does not prove it.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For every algebraic extension of fields `L/k` and every scheme `X` over `Spec k`, if the
base change of `X` to `Spec L` has the DVR lifting property over `L`, then `X` has the DVR
lifting property over `k`. -/
def DVRLiftingAlgebraicDescentStatement : Prop :=
  ∀ (k L : Type u) [Field k] [Field L] [Algebra k L] [Algebra.IsAlgebraic k L]
    (X : Over (Spec (CommRingCat.of k))),
    PseudoComplete.HasDVRLifting (k := L)
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap k L)))).obj X) →
      PseudoComplete.HasDVRLifting X

end Langlands.GroupScheme
