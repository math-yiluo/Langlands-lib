import Langlands.AbelianScheme.GeometricEndomorphismDegree
import Langlands.AbelianScheme.Rational
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # The geometric endomorphism degree polynomial law -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators

namespace Langlands.AbelianScheme

/-- Geometric degree extends to a normalized multiplicative rational function
whose restriction to every finite tuple is homogeneous polynomial of degree
twice the relative dimension. This is an unproved statement. -/
def GeometricEndomorphismDegreePolynomialStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k] [CharZero k]
    (A : AbelianScheme (Spec (CommRingCat.of k))) (g : ℕ),
    A.HasRelativeDimension g →
      ∃ delta : End0 A → ℚ,
        (∀ f : End A,
          delta (endToEnd0 A f) = (geometricEndomorphismDegree A f : ℚ)) ∧
        delta 1 = 1 ∧
        (∀ a b : End0 A, delta (a * b) = delta a * delta b) ∧
        ∀ (n : ℕ) (a : Fin n → End0 A),
          ∃ P : MvPolynomial (Fin n) ℚ,
            P.IsHomogeneous (2 * g) ∧
              ∀ x : Fin n → ℚ,
                MvPolynomial.eval x P = delta (∑ i : Fin n, x i • a i)

end Langlands.AbelianScheme
