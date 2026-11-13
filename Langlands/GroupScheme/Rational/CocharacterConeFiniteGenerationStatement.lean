import Langlands.GroupScheme.Rational.CocharacterCone
import Mathlib.GroupTheory.Finiteness

/-! # Finite generation of the nonnegative cocharacter quotient -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For finitely many actual characters, the nonnegative cocharacter monoid
modulo their common integral annihilator is finitely generated. -/
def CocharacterConeFiniteGenerationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (R : Set (characterLattice T)), R.Finite →
      (CocharacterCone.quotient T R).FG

end Langlands.GroupScheme
