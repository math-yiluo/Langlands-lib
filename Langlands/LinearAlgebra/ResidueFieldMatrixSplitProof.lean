import Langlands.LinearAlgebra.ResidueFieldMatrixSplitStatement
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import Mathlib.RingTheory.Localization.Away.Basic

/-! # Matrix splitting near a prime -/

universe u

noncomputable section

namespace Langlands.LinearAlgebra

private theorem exists_row_minor_of_mulVec_injective
    {k : Type u} [Field k] {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) k)
    (hA : Function.Injective A.mulVec) :
    ∃ e : Fin n → Fin m, (A.submatrix e id).det ≠ 0 := by
  classical
  have hrank : A.rank = n := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj hA]
    simp
  have hspan : Submodule.span k (Set.range A.row) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by
      rw [← A.rank_eq_finrank_span_row, hrank]
      simp)
  have htop : ⊤ ≤ Submodule.span k (Set.range A.row) := hspan.ge
  let b := Module.Basis.ofSpan htop
  let c := b.reindex (b.indexEquiv (Pi.basisFun k (Fin n)))
  have hc (i : Fin n) : ∃ j : Fin m, A.row j = c i := by
    apply Module.Basis.ofSpan_subset htop
    exact ⟨(b.indexEquiv (Pi.basisFun k (Fin n))).symm i,
      (b.reindex_apply _ i).symm⟩
  choose e he using hc
  refine ⟨e, ?_⟩
  have hrows : (A.submatrix e id).row = c := by
    funext i
    exact he i
  have hunit : IsUnit (A.submatrix e id) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp (by
      rw [hrows]
      exact c.linearIndependent)
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hunit)

/-- A residue-field injective matrix splits after inverting a determinant outside the prime. -/
theorem residueFieldMatrixSplit_of_injective
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (m n : ℕ) (A : Matrix (Fin m) (Fin n) R)
    (hA : Function.Injective (A.map (algebraMap R p.ResidueField)).mulVec) :
    ∃ r : R, r ∉ p ∧
      ∃ B : Matrix (Fin n) (Fin m) (Localization.Away r),
        B * A.map (algebraMap R (Localization.Away r)) = 1 := by
  classical
  obtain ⟨e, he⟩ :=
    exists_row_minor_of_mulVec_injective (A.map (algebraMap R p.ResidueField)) hA
  let D := A.submatrix e id
  let r := D.det
  have hD : algebraMap R p.ResidueField D.det ≠ 0 := by
    rw [RingHom.map_det]
    exact he
  have hr : r ∉ p := by
    intro h
    exact hD (Ideal.algebraMap_residueField_eq_zero.mpr h)
  let C := D.map (algebraMap R (Localization.Away r))
  have hC : IsUnit C.det := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Localization.Away r) r
    change IsUnit (algebraMap R (Localization.Away r) D.det) at h
    rw [RingHom.map_det] at h
    exact h
  let E : Matrix (Fin n) (Fin m) (Localization.Away r) :=
    (1 : Matrix (Fin m) (Fin m) (Localization.Away r)).submatrix e
      (Equiv.refl (Fin m))
  have hEC : E * A.map (algebraMap R (Localization.Away r)) = C := by
    exact Matrix.one_submatrix_mul e (Equiv.refl (Fin m))
      (A.map (algebraMap R (Localization.Away r)))
  refine ⟨r, hr, C⁻¹ * E, ?_⟩
  rw [Matrix.mul_assoc, hEC]
  exact C.nonsing_inv_mul hC

/-- The exact matrix-splitting statement over every commutative ring and universe. -/
theorem residueFieldMatrixSplit : ResidueFieldMatrixSplitStatement.{u} :=
  residueFieldMatrixSplit_of_injective

end Langlands.LinearAlgebra
