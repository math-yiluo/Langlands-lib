import Langlands.GroupScheme.Quaternionic.MatrixReducedNorm
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! # Reduced norm of a rank-one matrix update -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

open FiniteAlgebraUnits.MatrixPoints Langlands.CentralSimple

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1500000

section RankOne

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D]
  {I : Type} [Fintype I] [DecidableEq I] [Nonempty I]

/-- The reduced norm of the identity minus a rank-one product is the
  coefficient reduced norm of the identity minus its contracted product. -/
theorem matrixReducedNorm_one_sub_vecMulVec (R : Type u) [CommRing R] [Algebra F R]
    (x y : I → R ⊗[F] D) :
    matrixReducedNorm R (1 - vecMulVec x y) = reducedNorm F D R (1 - y ⬝ᵥ x) := by
  let L := AlgebraicClosure F
  let e := algebraicClosureChart F D
  let q := reducedDegree F D
  let S := L ⊗[F] R
  let f : R →ₐ[F] S := Algebra.TensorProduct.includeRight
  let g := Algebra.TensorProduct.map f (AlgHom.id F D)
  apply Algebra.TensorProduct.includeRight_injective (algebraMap F L).injective
  change f _ = f _
  rw [← matrixReducedNorm_naturality f, ← reducedNorm_naturality F D f]
  have hmat : (1 - vecMulVec x y).map g = 1 - vecMulVec (g ∘ x) (g ∘ y) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.sub_apply, Matrix.vecMulVec_apply, _root_.map_sub, _root_.map_mul,
      Function.comp_apply]
    rw [← Matrix.map_apply (M := (1 : Matrix I I (R ⊗[F] D))) (f := g),
      Matrix.map_one g (map_zero g) (map_one g)]
  have hsc : g (1 - y ⬝ᵥ x) = 1 - (g ∘ y) ⬝ᵥ (g ∘ x) := by
    simp only [dotProduct, map_sub, map_one, map_sum, map_mul, Function.comp_apply]
  change matrixReducedNorm S ((1 - vecMulVec x y).map g) = reducedNorm F D S (g (1 - y ⬝ᵥ x))
  rw [hmat, hsc]
  let ψ := (coefficientEquiv (m := I) F D S).symm.toRingEquiv.trans (DegreeSplitting.matrixChartR e S)
  let φ := DegreeSplitting.chartR e S
  change reducedNorm F (Matrix I I D) S ((coefficientEquiv F D S).symm (1 - vecMulVec (g ∘ x) (g ∘ y))) = _
  rw [DegreeSplitting.reducedNorm_eq_det_matrixChartR e, reducedNorm_eq_det F D e S]
  change (ψ (1 - vecMulVec (g ∘ x) (g ∘ y))).det = (φ (1 - (g ∘ y) ⬝ᵥ (g ∘ x))).det
  let A : Matrix (I × Fin q) (Fin q) S := Matrix.of fun ⟨i, a⟩ b => φ (g (x i)) a b
  let B : Matrix (Fin q) (I × Fin q) S := Matrix.of fun a ⟨j, b⟩ => φ (g (y j)) a b
  have hAB : ψ (vecMulVec (g ∘ x) (g ∘ y)) = A * B := by
    ext ⟨i, a⟩ ⟨j, b⟩
    change DegreeSplitting.matrixChartR e S ((coefficientEquiv F D S).symm
      (vecMulVec (g ∘ x) (g ∘ y))) (i, a) (j, b) = _
    rw [DegreeSplitting.matrixChartR_apply, AlgEquiv.apply_symm_apply, Matrix.vecMulVec_apply]
    change φ (g (x i) * g (y j)) a b = (A * B) (i, a) (j, b)
    rw [map_mul]
    simp only [Matrix.mul_apply, A, B, Matrix.of_apply]
    rfl
  have hBA : φ ((g ∘ y) ⬝ᵥ (g ∘ x)) = B * A := by
    ext a b
    simp only [dotProduct, Function.comp_apply, map_sum, map_mul, Matrix.sum_apply,
      Matrix.mul_apply, Fintype.sum_prod_type, A, B, Matrix.of_apply]
    rfl
  rw [map_sub, map_one, hAB, map_sub, map_one, hBA, Matrix.det_one_sub_mul_comm]

/-- The reduced norm rank-one update identity for the original division coefficients. -/
theorem reducedNorm_matrix_one_sub_vecMulVec (x y : I → D) :
    reducedNorm F (Matrix I I D) F ((1 : F) ⊗ₜ[F] (1 - vecMulVec x y)) =
      reducedNorm F D F ((1 : F) ⊗ₜ[F] (1 - y ⬝ᵥ x)) := by
  let g : D →ₐ[F] F ⊗[F] D := Algebra.TensorProduct.includeRight
  let x' := g ∘ x
  let y' := g ∘ y
  have hM : coefficientEquiv F D F ((1 : F) ⊗ₜ[F] (1 - vecMulVec x y)) = 1 - vecMulVec x' y' := by
    ext i j
    rw [coefficientEquiv_tmul]
    change g ((1 - vecMulVec x y) i j) = _
    rw [Matrix.sub_apply, map_sub, Matrix.vecMulVec_apply, map_mul, Matrix.sub_apply, Matrix.vecMulVec_apply]
    congr 1
    by_cases h : i = j
    · subst j
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
  have hq : (1 : F) ⊗ₜ[F] (1 - y ⬝ᵥ x) = 1 - y' ⬝ᵥ x' := by
    change g (1 - y ⬝ᵥ x) = _
    simp only [dotProduct, map_sub, map_one, map_sum, map_mul, x', y', Function.comp_apply]
  have h := matrixReducedNorm_one_sub_vecMulVec F x' y'
  rw [← hM, ← hq] at h
  change reducedNorm F (Matrix I I D) F ((coefficientEquiv F D F).symm
    (coefficientEquiv F D F ((1 : F) ⊗ₜ[F] (1 - vecMulVec x y)))) = _ at h
  simpa only [AlgEquiv.symm_apply_apply] using h

end RankOne

/-- The rectangular determinant identity for the reduced norm of a rank-one
  update, over an arbitrary commutative scalar algebra. -/
def RankOneReducedNormStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [DivisionRing D] [Algebra F D] [Algebra.IsCentral F D]
    [FiniteDimensional F D] [CommRing R] [Algebra F R] (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
    (x y : I → R ⊗[F] D),
    matrixReducedNorm R (1 - vecMulVec x y) = reducedNorm F D R (1 - y ⬝ᵥ x)

theorem rankOneReducedNorm : RankOneReducedNormStatement.{u} := by
  intro F D R _ _ _ _ _ _ _ I _ _ _ x y
  exact matrixReducedNorm_one_sub_vecMulVec R x y

end Langlands.GroupScheme.Quaternionic
