import Langlands.LinearAlgebra.FiniteBasisDeterminant
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Determinant units of finite product bases -/

noncomputable section

universe u v w z

namespace Langlands.LinearAlgebra.FiniteBasisDeterminant

variable {R : Type u} [CommRing R]
    {M : Type v} [AddCommGroup M] [Module R M]
    {N : Type w} [AddCommGroup N] [Module R N]

/-- The product basis with the standard finite index of the sum of the ranks. -/
def productBasis {n m : ℕ} (a : Module.Basis (Fin n) R M)
    (b : Module.Basis (Fin m) R N) : Module.Basis (Fin (n + m)) R (M × N) :=
  (a.prod b).reindex finSumFinEquiv

/-- Product basis transition matrices have the two original matrices as their
only nonzero diagonal blocks, after the simultaneous standard index change. -/
theorem productBasis_toMatrix {n m : ℕ}
    (a a' : Module.Basis (Fin n) R M) (b b' : Module.Basis (Fin m) R N) :
    (productBasis a b).toMatrix (productBasis a' b') =
      (Matrix.fromBlocks (a.toMatrix a') 0 0 (b.toMatrix b')).submatrix
        finSumFinEquiv.symm finSumFinEquiv.symm := by
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  cases i <;> cases j <;>
    simp [productBasis, Module.Basis.toMatrix_apply, Module.Basis.prod_apply]

/-- The determinant of a product transition is the product of the two determinants. -/
theorem det_productBasis_toMatrix {n m : ℕ}
    (a a' : Module.Basis (Fin n) R M) (b b' : Module.Basis (Fin m) R N) :
    ((productBasis a b).toMatrix (productBasis a' b')).det =
      (a.toMatrix a').det * (b.toMatrix b').det := by
  rw [productBasis_toMatrix, Matrix.det_submatrix_equiv_self,
    Matrix.det_fromBlocks_zero₂₁]

/-- Mixed determinant units multiply for product bases, including unequal
rank indices over the trivial ring. -/
theorem unit_productBasis {n n' m m' : ℕ}
    (a : Module.Basis (Fin n) R M) (a' : Module.Basis (Fin n') R M)
    (b : Module.Basis (Fin m) R N) (b' : Module.Basis (Fin m') R N) :
    unit (productBasis a b) (productBasis a' b') = unit a a' * unit b b' := by
  by_cases ha : n = n'
  · subst n'
    by_cases hb : m = m'
    · subst m'
      apply Units.ext
      simp only [unit_same, sameUnit_val, Units.val_mul]
      exact det_productBasis_toMatrix a a' b b'
    · let : Subsingleton R := subsingleton_of_rank_ne b b' hb
      exact Subsingleton.elim _ _
  · let : Subsingleton R := subsingleton_of_rank_ne a a' ha
    exact Subsingleton.elim _ _

/-- Applying the same linear equivalence to both bases preserves the mixed
transition determinant unit. -/
theorem unit_map {P : Type z} [AddCommGroup P] [Module R P] {n m : ℕ}
    (a : Module.Basis (Fin n) R M) (b : Module.Basis (Fin m) R M) (E : M ≃ₗ[R] P) :
    unit (a.map E) (b.map E) = unit a b := by
  apply Units.ext
  symm
  exact map_unit (RingHom.id R) a b (a.map E) (b.map E) (by
    intro i j
    simp)

end Langlands.LinearAlgebra.FiniteBasisDeterminant
