import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRows

/-! # A fixed basis change in the coefficient row chart -/

noncomputable section
universe u
open Matrix Module
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.OrthogonalMorita

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [Field L] [Algebra K L]
  {m degree n : ℕ}
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin degree) (Fin degree) L)
  {P : Matrix (Fin n ⊕ Fin n) (Fin m × Fin degree) L}
  {P' : Matrix (Fin m × Fin degree) (Fin n ⊕ Fin n) L}
  (hPP' : P * P' = 1) (hP'P : P' * P = 1)

/-- Change every split row by the fixed inverse basis matrix. -/
def basisRowEquiv :
    L ⊗[K] (Fin m → D) ≃ₗ[L] (Fin degree → (Fin n ⊕ Fin n → L)) :=
  rowChart e L ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ : Fin degree =>
      Matrix.toLinearEquivRight'OfInv hPP' hP'P)

theorem basisRowEquiv_apply (z : L ⊗[K] (Fin m → D)) (j : Fin degree) :
    basisRowEquiv e hPP' hP'P z j = Matrix.vecMul (rowChart e L z j) P' := rfl

/-- Canonical scalar extension of the fixed row equivalence has the expected
coefficient formula over every compatible algebra. -/
theorem rowEquivOver_basisRowEquiv (R : Type u) [CommRing R] [Algebra K R]
    [Algebra L R] [IsScalarTower K L R] (z : R ⊗[K] (Fin m → D)) :
    rowEquivOver (basisRowEquiv e hPP' hP'P) R z =
      fun j => Matrix.vecMul (rowChart e R z j) (P'.map (algebraMap L R)) := by
  induction z with
  | tmul r v =>
    funext j x
    simp only [rowEquivOver_tmul, basisRowEquiv_apply, Matrix.vecMul, dotProduct,
      _root_.map_sum, _root_.map_mul, Matrix.map_apply, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro p _
    rcases p with ⟨i, b⟩
    simp only [rowChart_tmul, one_mul, Algebra.algebraMap_self, RingHom.id_apply]
    ring
  | add z w hz hw =>
    simp only [_root_.map_add, hz, hw, Pi.add_apply, Matrix.add_vecMul]
    rfl

/-- The fixed row basis intertwines right multiplication with conjugation of
the split matrix, over every compatible coefficient algebra. -/
theorem basisRowEquiv_rightAction (R : Type u) [CommRing R] [Algebra K R]
    [Algebra L R] [IsScalarTower K L R]
    (a : R ⊗[K] Matrix (Fin m) (Fin m) D) (z : R ⊗[K] (Fin m → D)) :
    rowEquivOver (basisRowEquiv e hPP' hP'P) R
        ((TensorProduct.piRight K R R (fun _ : Fin m => D)).symm
          (Matrix.vecMul (TensorProduct.piRight K R R (fun _ : Fin m => D) z)
            (TensorMatrix.equiv R (Fin m) a))) =
      fun j => Matrix.vecMul (rowEquivOver (basisRowEquiv e hPP' hP'P) R z j)
        (P.map (algebraMap L R) * DegreeSplitting.matrixChartR e R a *
          P'.map (algebraMap L R)) := by
  rw [rowEquivOver_basisRowEquiv, rowEquivOver_basisRowEquiv, rowChart_rightAction]
  funext j
  dsimp only
  rw [Matrix.vecMul_vecMul, Matrix.vecMul_vecMul]
  congr 1
  rw [← Matrix.mul_assoc (P'.map _), ← Matrix.mul_assoc (P'.map _),
    ← Matrix.map_mul, hP'P, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]

end Langlands.GroupScheme.Quaternionic.OrthogonalMorita
