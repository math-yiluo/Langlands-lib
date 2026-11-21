import Langlands.GroupScheme.Quaternionic.SkewHermitianAdjoinLine
import Langlands.GroupScheme.Quaternionic.MatrixReducedNorm

/-! # Matrix stabilizer of an adjoined nonsingular skew line -/

noncomputable section

universe u v

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

section Matrix

variable {A : Type v} [Ring A] {n : ℕ}

/-- Products of square block diagonal matrices multiply each block. -/
theorem adjoinSkewLine_mul (P Q : Matrix (Fin n) (Fin n) A) (a b : A) :
    adjoinSkewLine P a * adjoinSkewLine Q b = adjoinSkewLine (P * Q) (a * b) := by
  simp only [adjoinSkewLine, ← map_mul, Matrix.fromBlocks_multiply, Matrix.mul_zero,
    Matrix.zero_mul, add_zero, zero_add, Matrix.diagonal_mul_diagonal]

private theorem single_last_vecMul_adjoinSkewLine
    (P : Matrix (Fin n) (Fin n) A) (a : A) :
    (Pi.single (Fin.last n) (1 : A)) ᵥ* adjoinSkewLine P a = Pi.single (Fin.last n) a := by
  rw [Matrix.single_one_vecMul]
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [Matrix.row_apply, adjoinSkewLine_last, Pi.single_eq_same]
  · simp only [Matrix.row_apply, adjoinSkewLine_last_castSucc, Pi.single_eq_of_ne (Fin.castSucc_ne_last j)]

private theorem isUnit_of_adjoinSkewLine_one {P : Matrix (Fin n) (Fin n) A}
    (hP : IsUnit (adjoinSkewLine P (1 : A))) : IsUnit P := by
  let Q := (↑hP.unit⁻¹ : Matrix (Fin (n + 1)) (Fin (n + 1)) A).submatrix Fin.castSucc Fin.castSucc
  have hPQ : P * Q = 1 := by
    ext i j
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) A =>
      M i.castSucc j.castSucc) hP.mul_val_inv
    simpa only [Matrix.mul_apply, Fin.sum_univ_castSucc, adjoinSkewLine_castSucc,
      adjoinSkewLine_castSucc_last, zero_mul, add_zero, Q, Matrix.submatrix_apply,
      Matrix.one_apply, Fin.castSucc_inj] using h
  have hQP : Q * P = 1 := by
    ext i j
    have h := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) A =>
      M i.castSucc j.castSucc) hP.val_inv_mul
    simpa only [Matrix.mul_apply, Fin.sum_univ_castSucc, adjoinSkewLine_castSucc,
      adjoinSkewLine_last_castSucc, mul_zero, add_zero, Q, Matrix.submatrix_apply,
      Matrix.one_apply, Fin.castSucc_inj] using h
  exact ⟨⟨P, Q, hPQ, hQP⟩, rfl⟩

end Matrix

namespace FirstKindInvolution

variable {F : Type u} {A : Type v} [CommRing F] [Ring A] [Algebra F A] {n : ℕ}
  (τ : FirstKindInvolution F A)

/-- Taking the adjoint preserves the two diagonal blocks. -/
theorem matrix_adjoinSkewLine (P : Matrix (Fin n) (Fin n) A) (a : A) :
    τ.matrix (Fin (n + 1)) (adjoinSkewLine P a) = adjoinSkewLine (τ.matrix (Fin n) P) (τ a) := by
  ext i j
  rw [FirstKindInvolution.matrix_apply]
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp only [adjoinSkewLine_last, adjoinSkewLine_last_castSucc, adjoinSkewLine_castSucc_last,
        FirstKindInvolution.map_zero]
  · refine Fin.lastCases ?_ (fun j => ?_) j <;>
      simp only [adjoinSkewLine_castSucc, adjoinSkewLine_last_castSucc, adjoinSkewLine_castSucc_last,
        FirstKindInvolution.map_zero, FirstKindInvolution.matrix_apply]

/-- An isometry fixing the last standard row of the augmented Gram matrix
  is the identity on that line and an isometry on the complementary block. -/
theorem adjoinSkewLine_fix_last_iff (H : Matrix (Fin n) (Fin n) A) (c : A) (hc : IsUnit c)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A) (hu : IsUnit M) :
    (M * adjoinSkewLine H c * τ.matrix (Fin (n + 1)) M = adjoinSkewLine H c ∧
      (Pi.single (Fin.last n) (1 : A)) ᵥ* M = Pi.single (Fin.last n) 1) ↔
    ∃ P : Matrix (Fin n) (Fin n) A, IsUnit P ∧ P * H * τ.matrix (Fin n) P = H ∧
      M = adjoinSkewLine P 1 := by
  constructor
  · rintro ⟨hpres, hfix⟩
    have hr : M (Fin.last n) = Pi.single (Fin.last n) 1 := by
      rw [Matrix.single_one_vecMul] at hfix
      exact hfix
    have hr₀ (i : Fin n) : M (Fin.last n) i.castSucc = 0 := by
      simpa only [Pi.single_eq_of_ne (Fin.castSucc_ne_last i)] using congrFun hr i.castSucc
    have hr₁ : M (Fin.last n) (Fin.last n) = 1 := by
      simpa only [Pi.single_eq_same] using congrFun hr (Fin.last n)
    have hh (j : Fin (n + 1)) : (M * adjoinSkewLine H c) (Fin.last n) j =
        adjoinSkewLine H c (Fin.last n) j := by
      simp only [Matrix.mul_apply, Fin.sum_univ_castSucc, hr₀, hr₁, zero_mul, one_mul,
        Finset.sum_const_zero, zero_add]
    have hc₀ (i : Fin n) : M i.castSucc (Fin.last n) = 0 := by
      have h := congrArg (fun P : Matrix (Fin (n + 1)) (Fin (n + 1)) A =>
        P (Fin.last n) i.castSucc) hpres
      have h' : c * τ (M i.castSucc (Fin.last n)) = 0 := by
        simpa only [Matrix.mul_apply, Fin.sum_univ_castSucc, hh, adjoinSkewLine_last_castSucc,
          adjoinSkewLine_last, zero_mul, Finset.sum_const_zero, zero_add,
          FirstKindInvolution.matrix_apply] using h
      have h'' := congrArg (fun a : A => (↑hc.unit⁻¹ : A) * a) h'
      rw [← mul_assoc, hc.val_inv_mul, one_mul, mul_zero] at h''
      exact τ.injective (h''.trans (τ.map_zero).symm)
    let P := M.submatrix Fin.castSucc Fin.castSucc
    have hM : M = adjoinSkewLine P 1 := by
      ext i j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · refine Fin.lastCases ?_ (fun j => ?_) j <;>
          simp only [hr₀, hr₁, adjoinSkewLine_last, adjoinSkewLine_last_castSucc]
      · refine Fin.lastCases ?_ (fun j => ?_) j <;>
          simp only [hc₀, adjoinSkewLine_castSucc_last, adjoinSkewLine_castSucc, P,
            Matrix.submatrix_apply]
    refine ⟨P, isUnit_of_adjoinSkewLine_one (hM ▸ hu), ?_, hM⟩
    rw [hM, τ.matrix_adjoinSkewLine, adjoinSkewLine_mul, adjoinSkewLine_mul, τ.map_one,
      one_mul, mul_one] at hpres
    ext i j
    simpa only [adjoinSkewLine_castSucc] using congrArg
      (fun N : Matrix (Fin (n + 1)) (Fin (n + 1)) A => N i.castSucc j.castSucc) hpres
  · rintro ⟨P, _, hP, rfl⟩
    exact ⟨by rw [τ.matrix_adjoinSkewLine, adjoinSkewLine_mul, adjoinSkewLine_mul, τ.map_one,
      one_mul, mul_one, hP], single_last_vecMul_adjoinSkewLine P 1⟩

end FirstKindInvolution

section ReducedNorm

open FiniteAlgebraUnits.MatrixPoints Langlands.CentralSimple

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] [Algebra.IsCentral F D] {n : ℕ} [NeZero n]

/-- The isometry extension by the identity on a line preserves the reduced norm. -/
theorem matrixReducedNorm_adjoinSkewLine_one (R : Type u) [CommRing R] [Algebra F R]
    (P : Matrix (Fin n) (Fin n) (R ⊗[F] D)) :
    matrixReducedNorm R (adjoinSkewLine P 1) = matrixReducedNorm R P := by
  let L := AlgebraicClosure F
  let e := algebraicClosureChart F D
  let S := L ⊗[F] R
  let f : R →ₐ[F] S := Algebra.TensorProduct.includeRight
  let g := Algebra.TensorProduct.map f (AlgHom.id F D)
  apply Algebra.TensorProduct.includeRight_injective (algebraMap F L).injective
  change f _ = f _
  rw [← matrixReducedNorm_naturality f, ← matrixReducedNorm_naturality f]
  change matrixReducedNorm S ((adjoinSkewLine P 1).map g.toRingHom) =
    matrixReducedNorm S (P.map g.toRingHom)
  rw [map_adjoinSkewLine g.toRingHom, g.toRingHom.map_one]
  let chart {m : ℕ} (M : Matrix (Fin m) (Fin m) (S ⊗[F] D)) :=
    DegreeSplitting.matrixChartR e S ((coefficientEquiv F D S).symm M)
  let U := chart (adjoinSkewLine (P.map g) 1)
  let V := chart (P.map g)
  let W := chart (1 : Matrix (Fin 1) (Fin 1) (S ⊗[F] D))
  change reducedNorm F _ S ((coefficientEquiv F D S).symm (adjoinSkewLine (P.map g) 1)) =
    reducedNorm F _ S ((coefficientEquiv F D S).symm (P.map g))
  rw [DegreeSplitting.reducedNorm_eq_det_matrixChartR e, DegreeSplitting.reducedNorm_eq_det_matrixChartR e]
  change U.det = V.det
  let J := Fin (reducedDegree F D)
  let η : (Fin (n + 1) × J) ≃ (Fin n × J) ⊕ (Fin 1 × J) :=
    (Equiv.prodCongr finSumFinEquiv.symm (Equiv.refl J)).trans (Equiv.sumProdDistrib _ _ _)
  have hleft (i : Fin n) (a : J) : η.symm (.inl (i, a)) = (i.castSucc, a) := rfl
  have hright (i : Fin 1) (a : J) : η.symm (.inr (i, a)) = (Fin.last n, a) := by
    rw [Subsingleton.elim i 0]
    rfl
  have hchart {m : ℕ} (M : Matrix (Fin m) (Fin m) (S ⊗[F] D)) (i j : Fin m) (a b : J) :
      chart M (i, a) (j, b) = DegreeSplitting.chartR e S (M i j) a b := by
    dsimp only [chart]
    rw [DegreeSplitting.matrixChartR_apply, AlgEquiv.apply_symm_apply]
  have hblock : Matrix.reindex η η U = Matrix.fromBlocks V 0 0 W := by
    ext (⟨i, a⟩ | ⟨i, a⟩) (⟨j, b⟩ | ⟨j, b⟩)
    · change U (η.symm (.inl (i, a))) (η.symm (.inl (j, b))) = V (i, a) (j, b)
      rw [hleft, hleft]
      dsimp only [U, V]
      rw [hchart, hchart, adjoinSkewLine_castSucc]
    · change U (η.symm (.inl (i, a))) (η.symm (.inr (j, b))) = 0
      rw [hleft, hright]
      dsimp only [U]
      rw [hchart, adjoinSkewLine_castSucc_last, map_zero, Matrix.zero_apply]
    · change U (η.symm (.inr (i, a))) (η.symm (.inl (j, b))) = 0
      rw [hright, hleft]
      dsimp only [U]
      rw [hchart, adjoinSkewLine_last_castSucc, map_zero, Matrix.zero_apply]
    · change U (η.symm (.inr (i, a))) (η.symm (.inr (j, b))) = W (i, a) (j, b)
      rw [hright, hright]
      dsimp only [U, W]
      rw [hchart, hchart, adjoinSkewLine_last, Subsingleton.elim j i, Matrix.one_apply_eq]
  have hW : W = 1 := by
    dsimp only [W, chart]
    rw [map_one, map_one]
  rw [← Matrix.det_reindex_self η U, hblock, Matrix.det_fromBlocks_zero₂₁, hW, Matrix.det_one, mul_one]

end ReducedNorm

/-- A norm-one isometry fixing the last basis row is extension by the identity
  of a norm-one isometry of the complementary Gram block. -/
def SkewLineStabilizerStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] [CommRing R] [Algebra F R]
    (τ : FirstKindInvolution F D) (n : ℕ) [NeZero n],
    let A := R ⊗[F] D
    let σ := τ.baseChange R
    ∀ (H : Matrix (Fin n) (Fin n) A) (c : A), IsUnit c →
    ∀ (M : Matrix (Fin (n + 1)) (Fin (n + 1)) A), IsUnit M →
    ((M * adjoinSkewLine H c * σ.matrix (Fin (n + 1)) M = adjoinSkewLine H c ∧
      matrixReducedNorm R M = 1 ∧
      (Pi.single (Fin.last n) (1 : A)) ᵥ* M = Pi.single (Fin.last n) 1) ↔
    ∃ P : Matrix (Fin n) (Fin n) A, IsUnit P ∧ P * H * σ.matrix (Fin n) P = H ∧
      matrixReducedNorm R P = 1 ∧ M = adjoinSkewLine P 1)

theorem skewLineStabilizer : SkewLineStabilizerStatement.{u} := by
  intro F D R _ _ _ _ _ _ _ τ n _ A σ H c hc M hu
  constructor
  · rintro ⟨hpres, hnorm, hfix⟩
    obtain ⟨P, hP, hpp, hm⟩ := (σ.adjoinSkewLine_fix_last_iff H c hc M hu).mp ⟨hpres, hfix⟩
    rw [hm, matrixReducedNorm_adjoinSkewLine_one] at hnorm
    exact ⟨P, hP, hpp, hnorm, hm⟩
  · rintro ⟨P, hP, hpp, hnorm, hm⟩
    obtain ⟨ha, hb⟩ := (σ.adjoinSkewLine_fix_last_iff H c hc M hu).mpr ⟨P, hP, hpp, hm⟩
    refine ⟨ha, ?_, hb⟩
    rw [hm, matrixReducedNorm_adjoinSkewLine_one]
    exact hnorm

end Langlands.GroupScheme.Quaternionic
