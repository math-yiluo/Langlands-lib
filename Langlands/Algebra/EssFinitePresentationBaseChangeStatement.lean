import Langlands.Algebra.EssFinitePresentation
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Essential finite presentation under base change (Stacks 0AUF) -/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

/-- Stacks Project, Lemma 10.54.3 (tag 0AUF), essential-finite-presentation part:
base change along an arbitrary `R`-algebra preserves essential finite presentation.
The tensor product has its canonical left-factor `B`-algebra structure.
This defines the statement only. -/
def EssFinitePresentationBaseChangeStatement : Prop :=
  ∀ (R : Type u) (A : Type v) (B : Type w)
    [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B],
    EssFinitePresentation R A → EssFinitePresentation B (B ⊗[R] A)

end Langlands.Algebra
