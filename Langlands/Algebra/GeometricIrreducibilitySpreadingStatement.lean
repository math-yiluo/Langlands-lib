import Mathlib

/-!
# Affine algebraic geometric irreducibility spreading

An internal algebraic reformulation of the affine case of Stacks Project
Lemma 37.27.5 (0559). This module states the proposition; it does not prove it.

Authors: Worker 1606, Worker 1620
-/

universe u v w

open scoped TensorProduct

namespace Langlands.Algebra

/-- The affine algebraic core of geometric irreducibility spreading. -/
def FiniteTypeGeometricIrreducibilitySpreading : Prop :=
  ∀ (R : Type u) [CommRing R] [(nilradical R).IsPrime]
    (B : Type v) [CommRing B] [Algebra R B] [Algebra.FiniteType R B],
    (nilradical (AlgebraicClosure (nilradical R).ResidueField ⊗[R] B)).IsPrime →
      ∃ c : R, ¬ IsNilpotent c ∧
        ∀ (K : Type w) [Field K] (φ : R →+* K), φ c ≠ 0 →
          letI : Algebra R K := φ.toAlgebra
          (nilradical (K ⊗[R] B)).IsPrime

end Langlands.Algebra
