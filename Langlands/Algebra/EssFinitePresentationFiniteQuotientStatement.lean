import Langlands.Algebra.EssFinitePresentation
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Essential finite presentation under finitely generated ideal quotients -/

universe u v

namespace Langlands.Algebra

/-- A quotient of an essentially finitely presented algebra by a finitely generated
ideal is essentially finitely presented, with its canonical quotient algebra structure.
This derived statement is used in the proof of Stacks Project tag 05UV. -/
def EssFinitePresentationFiniteQuotientStatement : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (J : Ideal B),
    EssFinitePresentation R B → J.FG → EssFinitePresentation R (B ⧸ J)

end Langlands.Algebra
