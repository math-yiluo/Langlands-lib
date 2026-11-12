import Langlands.GroupScheme.Quaternionic.HyperbolicMatrixExtension

/-! # Extending isometries along a hyperbolic plane -/

noncomputable section

universe u v w w' w''

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme

namespace SplitMatrixExtension

variable {A : Type u} [Ring A] {m : Type v} {n : Type w}
  [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
  (E : Matrix m n A) (R : Matrix n m A) (h : E * R = 1)

include h in
theorem value_mul_retraction (M : Matrix m m A) :
    value E R M * R = R * M := by
  simp [value, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, h]

include h in
theorem value_mul_complement (M : Matrix m m A) :
    value E R M * (1 - R * E) = 1 - R * E := by
  have hEQ : E * (1 - R * E) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, h, Matrix.one_mul, sub_self]
  have hPR : (1 - R * E) * R = 0 := by
    simp [Matrix.sub_mul, Matrix.mul_assoc, h]
  have hPP : (1 - R * E) * (1 - R * E) = 1 - R * E := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hPR, Matrix.zero_mul, sub_zero]
  rw [value, Matrix.add_mul, hPP, Matrix.mul_assoc, hEQ, Matrix.mul_zero, zero_add]

end SplitMatrixExtension

namespace Quaternionic.SplitQuadraticExtension

variable {K : Type u} {A : Type v} [CommRing K] [Ring A] [Algebra K A]
  (τ : FirstKindInvolution K A)
  {l : Type w} {m : Type w'} {n : Type w''}
  [Fintype l] [Fintype m] [Fintype n]
  [DecidableEq l] [DecidableEq m] [DecidableEq n]

/-- Rectangular conjugate transpose over an arbitrary coefficient ring. -/
def adjoint (M : Matrix m n A) : Matrix n m A := fun i j => τ (M j i)

omit [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] in
@[simp] theorem adjoint_adjoint (M : Matrix m n A) :
    adjoint τ (adjoint τ M) = M := by
  ext i j
  exact τ.apply_apply _

omit [Fintype l] [Fintype n] [DecidableEq l] [DecidableEq m] [DecidableEq n] in
theorem adjoint_mul (M : Matrix l m A) (N : Matrix m n A) :
    adjoint τ (M * N) = adjoint τ N * adjoint τ M := by
  ext i j
  simp [adjoint, Matrix.mul_apply]

theorem adjoint_square (M : Matrix n n A) : adjoint τ M = τ.matrix n M := rfl

variable (E : Matrix m n A) (R : Matrix n m A) (h : E * R = 1)

include h in
/-- The ambient defect is the rectangular pullback of the small defect. -/
theorem defect (H M : Matrix m m A) (Q : Matrix n n A) :
    let U := SplitMatrixExtension.value E R M
    let P := 1 - R * E
    let Q' := R * H * adjoint τ R + P * Q * τ.matrix n P
    U * Q' * τ.matrix n U - Q' =
      R * (M * H * τ.matrix m M - H) * adjoint τ R := by
  dsimp only
  let U := SplitMatrixExtension.value E R M
  let P := 1 - R * E
  have hUR : U * R = R * M := SplitMatrixExtension.value_mul_retraction E R h M
  have hUP : U * P = P := SplitMatrixExtension.value_mul_complement E R h M
  have hRU : adjoint τ R * τ.matrix n U = τ.matrix m M * adjoint τ R := by
    simpa only [adjoint_mul, adjoint_square] using congrArg (adjoint τ) hUR
  have hPU : τ.matrix n P * τ.matrix n U = τ.matrix n P := by
    simpa only [FirstKindInvolution.map_mul] using congrArg (τ.matrix n) hUP
  have h1 : U * (R * H * adjoint τ R) * τ.matrix n U =
      R * (M * H * τ.matrix m M) * adjoint τ R := by
    calc
      _ = (U * R) * H * (adjoint τ R * τ.matrix n U) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUR, hRU]; simp only [Matrix.mul_assoc]
  have h2 : U * (P * Q * τ.matrix n P) * τ.matrix n U =
      P * Q * τ.matrix n P := by
    calc
      _ = (U * P) * Q * (τ.matrix n P * τ.matrix n U) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hUP, hPU]
  change U * (R * H * adjoint τ R + P * Q * τ.matrix n P) * τ.matrix n U -
    (R * H * adjoint τ R + P * Q * τ.matrix n P) = _
  rw [Matrix.mul_add, Matrix.add_mul, h1, h2]
  simp only [Matrix.mul_sub, Matrix.sub_mul]
  abel

include h in
/-- An alternating small defect gives an alternating ambient defect over every ring. -/
theorem defect_mem (H M : Matrix m m A) (Q : Matrix n n A)
    (hM : M * H * τ.matrix m M - H ∈ (τ.matrix m).alternatingSubspace) :
    let U := SplitMatrixExtension.value E R M
    let P := 1 - R * E
    let Q' := R * H * adjoint τ R + P * Q * τ.matrix n P
    U * Q' * τ.matrix n U - Q' ∈ (τ.matrix n).alternatingSubspace := by
  dsimp only
  rw [defect τ E R h]
  obtain ⟨W, hW⟩ := (τ.matrix m).mem_alternatingSubspace.mp hM
  apply (τ.matrix n).mem_alternatingSubspace.mpr
  refine ⟨R * W * adjoint τ R, ?_⟩
  rw [← hW]
  change R * W * adjoint τ R -
    adjoint τ (R * W * adjoint τ R) = _
  rw [adjoint_mul, adjoint_mul, adjoint_adjoint, adjoint_square]
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]

end Quaternionic.SplitQuadraticExtension

namespace Quaternionic.FirstKindInvolution

variable {K D : Type u} [Field K] [DivisionRing D] [Algebra K D]
  (σ : FirstKindInvolution K D) {n : Type w} [Fintype n] [DecidableEq n]
  (q : σ.QuadraticForms n) (e f : n → D)

/-- The actual matrix projection onto the polar orthogonal complement. -/
def planeComplement : Matrix n n D :=
  1 - planeRetraction σ q e f * planeInclusion e f

theorem vecMul_planeComplement (v : n → D) :
    v ᵥ* planeComplement σ q e f = σ.hyperbolicRemainder q e f v := by
  simp only [planeComplement, Matrix.vecMul_sub, Matrix.vecMul_one,
    ← Matrix.vecMul_vecMul, vecMul_planeRetraction, vecMul_planeInclusion,
    Matrix.cons_val_zero, Matrix.cons_val_one, hyperbolicRemainder_apply,
    hyperbolicProjection_apply]

theorem quadraticValue_hyperbolicForm (v : Fin 2 → D) :
    σ.quadraticValue v (BinaryScheme.hyperbolicForm σ) =
      (Submodule.Quotient.mk (v 0 * σ (v 1)) : D ⧸ σ.alternatingSubspace) := by
  simp [BinaryScheme.hyperbolicForm, BinaryAction.hyperbolicMatrix,
    quadraticValue_mk, sesqForm, Fin.sum_univ_two]

variable {σ q e f}

namespace IsHyperbolicPair

variable (h : σ.IsHyperbolicPair q e f)

include h in
/-- The actual quotient form is the sum of its plane and complementary pullbacks. -/
theorem quadratic_decomposition :
    σ.quadraticPullback (planeRetraction σ q e f) (BinaryScheme.hyperbolicForm σ) +
      σ.quadraticPullback (planeComplement σ q e f) q = q := by
  apply σ.quadraticValue_ext
  intro v
  rw [LinearMap.map_add, quadraticValue_quadraticPullback, quadraticValue_quadraticPullback,
    vecMul_planeComplement, quadraticValue_hyperbolicForm, vecMul_planeRetraction]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  exact (h.quadraticValue_decomposition v).symm

/-- A representative adapted to the actual hyperbolic direct sum. -/
def splitRepresentative : Matrix n n D :=
  planeRetraction σ q e f * (BinaryAction.hyperbolicMatrix : Matrix (Fin 2) (Fin 2) D) *
      σ.rectangularAdjoint (planeRetraction σ q e f) +
    planeComplement σ q e f * Quotient.out q * σ.matrix n (planeComplement σ q e f)

include h in
theorem mk_splitRepresentative :
    (Submodule.Quotient.mk (splitRepresentative (σ := σ) (q := q) (e := e) (f := f)) :
      σ.QuadraticForms n) = q := by
  change σ.quadraticPullback (planeRetraction σ q e f) (BinaryScheme.hyperbolicForm σ) +
    σ.quadraticPullback (planeComplement σ q e f)
      (Submodule.Quotient.mk (Quotient.out q)) = q
  rw [Submodule.Quotient.mk_out]
  exact h.quadratic_decomposition

include h in
/-- Extending a binary isometry by the identity preserves the full actual quadratic form. -/
theorem quadraticPullback_planeUnitsHom (g : (Matrix (Fin 2) (Fin 2) D)ˣ)
    (hg : σ.quadraticPullback (g : Matrix (Fin 2) (Fin 2) D)
      (BinaryScheme.hyperbolicForm σ) = BinaryScheme.hyperbolicForm σ) :
    σ.quadraticPullback (h.planeUnitsHom g : Matrix n n D) q = q := by
  have hUR :
      (h.planeUnitsHom g : Matrix n n D) * planeRetraction σ q e f =
        planeRetraction σ q e f * (g : Matrix (Fin 2) (Fin 2) D) :=
    SplitMatrixExtension.value_mul_retraction _ _ h.planeInclusion_mul_retraction _
  have hUP :
      (h.planeUnitsHom g : Matrix n n D) * planeComplement σ q e f =
        planeComplement σ q e f :=
    SplitMatrixExtension.value_mul_complement _ _ h.planeInclusion_mul_retraction _
  calc
    _ = σ.quadraticPullback (h.planeUnitsHom g : Matrix n n D)
        (σ.quadraticPullback (planeRetraction σ q e f) (BinaryScheme.hyperbolicForm σ) +
          σ.quadraticPullback (planeComplement σ q e f) q) := by
      rw [h.quadratic_decomposition]
    _ = σ.quadraticPullback
        ((h.planeUnitsHom g : Matrix n n D) * planeRetraction σ q e f)
          (BinaryScheme.hyperbolicForm σ) +
        σ.quadraticPullback
          ((h.planeUnitsHom g : Matrix n n D) * planeComplement σ q e f) q := by
      rw [LinearMap.map_add, ← quadraticPullback_mul, ← quadraticPullback_mul]
    _ = _ := by rw [hUR, hUP, quadraticPullback_mul, hg, h.quadratic_decomposition]

end IsHyperbolicPair

end Quaternionic.FirstKindInvolution

end Langlands.GroupScheme
