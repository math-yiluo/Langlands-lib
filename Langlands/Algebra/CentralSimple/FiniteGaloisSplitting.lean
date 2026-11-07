import Langlands.Algebra.CentralSimple.FiniteGaloisDescent
import Langlands.Algebra.CentralSimple.SeparableClosureChart

/-!
# Finite Galois matrix splitting of central simple algebras

A finite-dimensional central simple algebra over any field admits an actual
matrix chart over a finite Galois extension in the same universe.
-/

noncomputable section

universe u

namespace Langlands.CentralSimple

open scoped TensorProduct

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- A finite Galois intermediate field of the separable closure which splits
the central simple algebra. -/
def finiteGaloisSplittingIntermediateField :
    FiniteGaloisIntermediateField K (SeparableClosure K) :=
  finiteGaloisMatrixChartField (separableClosureChart K A)

/-- A chosen finite Galois splitting field in the base field's universe. -/
def finiteGaloisSplittingField : Type u :=
  (finiteGaloisSplittingIntermediateField K A).toIntermediateField

instance finiteGaloisSplittingField_field : Field (finiteGaloisSplittingField K A) :=
  inferInstanceAs (Field (finiteGaloisSplittingIntermediateField K A).toIntermediateField)

instance finiteGaloisSplittingField_algebra : Algebra K (finiteGaloisSplittingField K A) :=
  inferInstanceAs (Algebra K (finiteGaloisSplittingIntermediateField K A).toIntermediateField)

instance finiteGaloisSplittingField_finiteDimensional :
    FiniteDimensional K (finiteGaloisSplittingField K A) :=
  (finiteGaloisSplittingIntermediateField K A).finiteDimensional

instance finiteGaloisSplittingField_isGalois : IsGalois K (finiteGaloisSplittingField K A) :=
  (finiteGaloisSplittingIntermediateField K A).isGalois

/-- An actual matrix chart over the chosen finite Galois splitting field. -/
def finiteGaloisSplittingChart :
    finiteGaloisSplittingField K A ⊗[K] A ≃ₐ[finiteGaloisSplittingField K A]
      Matrix (Fin (reducedDegree K A)) (Fin (reducedDegree K A))
        (finiteGaloisSplittingField K A) :=
  finiteGaloisMatrixChart (separableClosureChart K A)

/-- The chosen chart has positive size and that size squared is the original
dimension. -/
theorem finiteGaloisSplittingChart_spec :
    0 < reducedDegree K A ∧
      Module.finrank K A = reducedDegree K A * reducedDegree K A :=
  ⟨reducedDegree_pos K A, finrank_eq_reducedDegree_mul_self K A⟩

/-- Every finite-dimensional central simple algebra has a finite Galois full
matrix splitting of positive size in the same universe. -/
theorem exists_finiteGalois_splitting :
    ∃ d : ℕ, 0 < d ∧ Module.finrank K A = d * d ∧
      ∃ (L : Type u) (_ : Field L) (_ : Algebra K L),
        FiniteDimensional K L ∧ IsGalois K L ∧
          Nonempty (L ⊗[K] A ≃ₐ[L] Matrix (Fin d) (Fin d) L) :=
  ⟨reducedDegree K A, reducedDegree_pos K A, finrank_eq_reducedDegree_mul_self K A,
    finiteGaloisSplittingField K A, inferInstance, inferInstance, inferInstance,
    inferInstance, ⟨finiteGaloisSplittingChart K A⟩⟩

end Langlands.CentralSimple
