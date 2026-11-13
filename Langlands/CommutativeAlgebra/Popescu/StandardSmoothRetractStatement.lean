import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.Smooth.StandardSmooth

/-! # Smooth algebras are retracts of standard smooth algebras -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

/-- Stacks Lemma 16.3.4 (07CH): if `A` is smooth over `R`, there is a smooth
`A`-algebra `B` admitting an `A`-algebra retraction `B → A` such that `B` is
standard smooth over `R`. -/
def StandardSmoothRetractStatement : Prop :=
  ∀ (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] [Algebra.Smooth R A],
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra R B) (_ : Algebra A B)
      (_ : IsScalarTower R A B),
      Algebra.Smooth A B ∧ Algebra.IsStandardSmooth R B ∧ Nonempty (B →ₐ[A] A)

end Langlands.CommutativeAlgebra.Popescu
