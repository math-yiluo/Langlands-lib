import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.RingTheory.Etale.Field

/-! # Finite representatives of bounded-dimensional étale algebras -/

namespace Langlands.LocalField

universe u v

/-- Finiteness of the finite extensions of degree at most `d` inside the
algebraic closure gives a finite family covering the isomorphism classes of
étale algebras of dimension at most `d`. -/
def BoundedEtaleAlgebraRepresentativesStatement : Prop :=
  ∀ (F : Type u) [Field F] (d : ℕ),
    {E : IntermediateField F (AlgebraicClosure F) |
      FiniteDimensional F E ∧ Module.finrank F E ≤ d}.Finite →
      ∃ (n : ℕ) (models : Fin n → Type u) (_ : ∀ j, CommRing (models j))
        (_ : ∀ j, Algebra F (models j)),
        ∀ (A : Type v) [CommRing A] [Algebra F A] [Algebra.Etale F A],
          Module.finrank F A ≤ d → ∃ j, Nonempty (A ≃ₐ[F] models j)

end Langlands.LocalField
