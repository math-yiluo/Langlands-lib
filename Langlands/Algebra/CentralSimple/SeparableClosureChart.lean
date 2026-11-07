import Langlands.Algebra.CentralSimpleScalarExtension
import Langlands.Algebra.CentralSimple.SeparablyClosedSplitting

/-!
# Matrix splitting of a central simple algebra over a separable closure

A finite-dimensional central simple algebra `A` over `K` becomes a full matrix
algebra of size `reducedDegree K A` over `SeparableClosure K`.
-/

noncomputable section

namespace Langlands.CentralSimple

universe uK uA uE

open scoped TensorProduct

variable (K : Type uK) [Field K] (A : Type uA) [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- A finite-dimensional central simple algebra splits, at its reduced degree, over every
separably closed extension field. -/
def sepClosedExtensionChart (E : Type uE) [Field E] [Algebra K E] [IsSepClosed E] :
    (E ⊗[K] A) ≃ₐ[E] Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) E :=
  have : IsSimpleRing (E ⊗[K] A) := isSimpleRing_baseChange K A E
  have : Algebra.IsCentral E (E ⊗[K] A) := isCentral_baseChange K A E
  (sepClosedChart E (E ⊗[K] A)).trans
    (Matrix.reindexAlgEquiv E E (finCongr (reducedDegree_baseChange K A E)))

/-- A chosen matrix chart of a finite-dimensional central simple algebra over the separable
closure of its base field, of size the reduced degree. -/
def separableClosureChart :
    (SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
      Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A)) (SeparableClosure K) :=
  sepClosedExtensionChart K A (SeparableClosure K)

/-- A finite-dimensional central simple algebra becomes a nonzero full matrix algebra over
the separable closure of its base field. -/
theorem exists_separableClosure_matrix_chart :
    ∃ d : ℕ, 0 < d ∧ Module.finrank K A = d * d ∧
      Nonempty ((SeparableClosure K ⊗[K] A) ≃ₐ[SeparableClosure K]
        Matrix (Fin d) (Fin d) (SeparableClosure K)) :=
  ⟨reducedDegree K A, reducedDegree_pos K A, finrank_eq_reducedDegree_mul_self K A,
    ⟨separableClosureChart K A⟩⟩

end Langlands.CentralSimple
