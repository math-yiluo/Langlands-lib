import Langlands.Algebra.LocalApproximationSystem
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # Existence of local base-ring approximation systems (base step of Stacks 00QV) -/

universe u v

namespace Langlands.Algebra

/-- Every commutative local ring `R` admits a directed local approximation system over the
identity algebra `R → R` (`Algebra.id`, made local by `isLocalHom_id`) satisfying all four
clauses of `LocalAlgebraSystem.IsApproximation`. This is the base-ring approximation used in
the proof of Stacks 00QV. The auxiliary universe `v` only allows the index and component
witnesses to be chosen in `Type (max u v)`. -/
def LocalRingApproximationExistenceStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsLocalRing R],
    haveI : IsLocalHom (algebraMap R R) := isLocalHom_id R
    ∃ (ι : Type (max u v)) (_ : Preorder ι) (_ : Nonempty ι)
      (_ : IsDirectedOrder ι)
      (D : LocalAlgebraSystem.{max u v, max u v, max u v, u, u} ι R R),
      D.IsApproximation

end Langlands.Algebra
