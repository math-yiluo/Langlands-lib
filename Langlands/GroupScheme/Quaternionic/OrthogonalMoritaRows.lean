import Langlands.GroupScheme.Quaternionic.OrthogonalMoritaRepresentationStatement
import Langlands.GroupScheme.Quaternionic.DegreeSplittingMatrix

/-! # Rows in an arbitrary-degree splitting chart -/

noncomputable section
universe u
open Matrix Module
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.OrthogonalMorita

variable {K D L : Type u} [Field K] [DivisionRing D] [Algebra K D]
  [Field L] [Algebra K L]
  {m degree n : ℕ}
  (e : L ⊗[K] D ≃ₐ[L] Matrix (Fin degree) (Fin degree) L)

/-- The coefficient splitting chart as an equivalence linear over its coefficient ring. -/
def coefficientLinear (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] :
    R ⊗[K] D ≃ₗ[R] Matrix (Fin degree) (Fin degree) R :=
  (AlgEquiv.ofBijective (ReducedNorm.splittingMap e R)
    (DegreeSplitting.bijective_splittingMap e R)).toLinearEquiv

/-- Regard a row of square blocks as a family of ordinary rows. -/
def reshapeRows (R : Type u) [CommRing R] :
    (Fin m → Matrix (Fin degree) (Fin degree) R) ≃ₗ[R]
      (Fin degree → (Fin m × Fin degree → R)) where
  toFun v j p := v p.1 j p.2
  invFun v i j b := v j (i, b)
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual row chart over a compatible coefficient algebra. -/
def rowChart (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] :
    R ⊗[K] (Fin m → D) ≃ₗ[R] (Fin degree → (Fin m × Fin degree → R)) :=
  TensorProduct.piRight K R R (fun _ : Fin m => D) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => coefficientLinear e R) ≪≫ₗ reshapeRows R

@[simp] theorem rowChart_apply (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] (z : R ⊗[K] (Fin m → D)) (j : Fin degree)
    (i : Fin m) (b : Fin degree) :
    rowChart e R z j (i, b) =
      DegreeSplitting.chartR e R
        (TensorProduct.piRight K R R (fun _ : Fin m => D) z i) j b := rfl

@[simp] theorem rowChart_tmul (R : Type u) [CommRing R] [Algebra K R] [Algebra L R]
    [IsScalarTower K L R] (r : R) (v : Fin m → D) (j : Fin degree)
    (i : Fin m) (b : Fin degree) :
    rowChart e R (r ⊗ₜ[K] v) j (i, b) =
      r * algebraMap L R (e (1 ⊗ₜ[K] v i) j b) := rfl

/-- The two entrywise tensor-matrix equivalences give the same coefficient chart. -/
theorem matrixChartR_apply_tensorMatrix (R : Type u) [CommRing R] [Algebra K R]
    [Algebra L R] [IsScalarTower K L R]
    (a : R ⊗[K] Matrix (Fin m) (Fin m) D) (i k : Fin m) (b c : Fin degree) :
    DegreeSplitting.matrixChartR e R a (i,b) (k,c) =
      DegreeSplitting.chartR e R (TensorMatrix.equiv R (Fin m) a i k) b c := by
  induction a using TensorProduct.inductionOn with
  | tmul r a =>
    rw [DegreeSplitting.matrixChartR_tmul_apply, TensorMatrix.equiv_tmul]
    rfl
  | add a a' ha ha' => simp only [_root_.map_add, Matrix.add_apply, ha, ha']

/-- Multiplication of rows of blocks becomes ordinary right multiplication on each row. -/
theorem chart_vecMul (R : Type u) [CommRing R] [Algebra K R]
    [Algebra L R] [IsScalarTower K L R]
    (a : R ⊗[K] Matrix (Fin m) (Fin m) D) (v : Fin m → R ⊗[K] D)
    (j : Fin degree) :
    (fun p : Fin m × Fin degree => DegreeSplitting.chartR e R
        (Matrix.vecMul v (TensorMatrix.equiv R (Fin m) a) p.1) j p.2) =
      Matrix.vecMul (fun p : Fin m × Fin degree => DegreeSplitting.chartR e R (v p.1) j p.2)
        (DegreeSplitting.matrixChartR e R a) := by
  funext p
  rcases p with ⟨i, b⟩
  simp only [Matrix.vecMul, dotProduct, _root_.map_sum, _root_.map_mul,
    Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type,
    matrixChartR_apply_tensorMatrix]

/-- The tensor row chart intertwines the actual right matrix action. -/
theorem rowChart_rightAction (R : Type u) [CommRing R] [Algebra K R]
    [Algebra L R] [IsScalarTower K L R]
    (a : R ⊗[K] Matrix (Fin m) (Fin m) D) (z : R ⊗[K] (Fin m → D)) :
    rowChart e R
        ((TensorProduct.piRight K R R (fun _ : Fin m => D)).symm
          (Matrix.vecMul (TensorProduct.piRight K R R (fun _ : Fin m => D) z)
            (TensorMatrix.equiv R (Fin m) a))) =
      fun j => Matrix.vecMul (rowChart e R z j) (DegreeSplitting.matrixChartR e R a) := by
  funext j p
  rcases p with ⟨i, b⟩
  have hr : rowChart e R z j = fun p : Fin m × Fin degree =>
      DegreeSplitting.chartR e R
        (TensorProduct.piRight K R R (fun _ : Fin m => D) z p.1) j p.2 := by
    funext ⟨i, b⟩
    rfl
  rw [hr]
  have h := chart_vecMul e R a (TensorProduct.piRight K R R (fun _ : Fin m => D) z) j
  simpa only [rowChart_apply, LinearEquiv.apply_symm_apply] using congrFun h (i, b)

end Langlands.GroupScheme.Quaternionic.OrthogonalMorita
