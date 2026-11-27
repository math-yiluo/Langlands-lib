import Langlands.BaseChange.RegularNormCentralizerAlgebra
import Mathlib.RingTheory.Etale.StandardEtale

/-! # The étale centralizer algebra of a regular matrix -/

open Polynomial

namespace Langlands.BaseChange

universe u

/-- For separable characteristic polynomial, its quotient algebra is étale
of the matrix size and evaluation identifies it with the matrix commutant. -/
def RegularMatrixCentralizerAlgebraStatement : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ) (A : Matrix (Fin n) (Fin n) F),
    A.charpoly.Separable →
      Algebra.Etale F (AdjoinRoot A.charpoly) ∧
      Module.finrank F (AdjoinRoot A.charpoly) = n ∧
      Function.Injective (charpolyRootEvaluation A) ∧
      ∀ B : Matrix (Fin n) (Fin n) F,
        B ∈ Set.range (charpolyRootEvaluation A) ↔ Commute B A

end Langlands.BaseChange
