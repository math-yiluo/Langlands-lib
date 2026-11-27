import Langlands.BaseChange.RegularNormCentralizerAlgebra

/-! # Conjugacy of regular matrix centralizer algebras -/

open Polynomial

namespace Langlands.BaseChange

universe u

/-- An isomorphism of characteristic-polynomial algebras of matrices with
separable characteristic polynomial is induced on their evaluated images
by conjugation by an invertible matrix over the ground field. -/
def RegularCentralizerAlgebraConjugacyStatement : Prop :=
  ∀ (F : Type u) [Field F] (n : ℕ) (A B : Matrix (Fin n) (Fin n) F),
    A.charpoly.Separable → B.charpoly.Separable →
      ∀ e : AdjoinRoot A.charpoly ≃ₐ[F] AdjoinRoot B.charpoly,
        ∃ g : GeneralLinear n F, ∀ a : AdjoinRoot A.charpoly,
          (g : Matrix (Fin n) (Fin n) F) * charpolyRootEvaluation A a *
              ((g⁻¹ : GeneralLinear n F) : Matrix (Fin n) (Fin n) F) =
            charpolyRootEvaluation B (e a)

end Langlands.BaseChange
