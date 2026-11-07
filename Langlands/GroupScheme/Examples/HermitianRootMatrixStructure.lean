import Langlands.GroupScheme.Examples.HermitianRootMatrices

/-! # Image and diagonal normalization of Hermitian root matrices -/

namespace Langlands.GroupScheme.HermitianRoot

open SU3Root

universe u v

variable {A : Type u} {ι : Type v}
  [CommRing A] [Fintype ι] [DecidableEq ι] {c : RingInvolution A}

/-- An upper block-unipotent matrix, with independent row and column coordinates. -/
def upperBlockMatrix (a b : ι → A) (z : A) : Matrix (Index ι) (Index ι) A :=
  Matrix.fromBlocks 1
    (Matrix.of fun _ j => Sum.elim a (fun _ => z) j)
    0
    (Matrix.fromBlocks 1 (Matrix.of fun i _ => b i) 0 1)

/-- The upper block-unipotent shape, with identity middle block. -/
def IsUpperBlockUnipotent (M : Matrix (Index ι) (Index ι) A) : Prop :=
  ∃ a b z, M = upperBlockMatrix a b z

namespace Parameters

variable {H : DiagonalForm c ι}

theorem matrix_upperBlockUnipotent (x : Parameters H) :
    IsUpperBlockUnipotent (matrix x) :=
  ⟨fun i => H.weight i * x.vector i, fun i => c.bar (x.vector i), x.scalar, rfl⟩

/-- The image consists exactly of upper block-unipotent form preservers. -/
theorem mem_range_embedding (g : Matrix.GeneralLinearGroup (Index ι) A) :
    g ∈ (embedding H).range ↔
      IsUpperBlockUnipotent (g : Matrix (Index ι) (Index ι) A) ∧
        PreservesForm H (g : Matrix (Index ι) (Index ι) A) := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨matrix_upperBlockUnipotent x, matrix_preservesForm x⟩
  · rintro ⟨⟨a, b, z, hshape⟩, hform⟩
    unfold PreservesForm at hform
    rw [hshape] at hform
    have hrow : ∀ i, a i = H.weight i * c.bar (b i) := by
      intro i
      have hi := congrArg (fun M : Matrix (Index ι) (Index ι) A =>
        M (Sum.inr (Sum.inl i)) (Sum.inr (Sum.inr ()))) hform
      simp [conjugateTranspose, gram, upperBlockMatrix, Matrix.fromBlocks,
        Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply,
        Matrix.diagonal_apply] at hi
      have hb := congrArg c.bar hi
      simp only [map_add, map_neg, map_mul, H.bar_weight,
        RingInvolution.bar_bar, map_zero] at hb
      linear_combination hb
    have hz : z + c.bar z =
        H.pairing (fun i => c.bar (b i)) (fun i => c.bar (b i)) := by
      have hi := congrArg (fun M : Matrix (Index ι) (Index ι) A =>
        M (Sum.inr (Sum.inr ())) (Sum.inr (Sum.inr ()))) hform
      simp [conjugateTranspose, gram, upperBlockMatrix, Matrix.fromBlocks,
        Matrix.mul_apply, Fintype.sum_sum_type,
        Matrix.diagonal_apply] at hi
      have hp : (∑ i, c.bar (b i) * H.weight i * b i) =
          H.pairing (fun i => c.bar (b i)) (fun i => c.bar (b i)) := by
        simp only [DiagonalForm.pairing, RingInvolution.bar_bar]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hp] at hi
      linear_combination hi
    let x : Parameters H := ⟨(fun i => c.bar (b i), z), hz⟩
    refine ⟨x, ?_⟩
    apply Units.ext
    change matrix x = (g : Matrix (Index ι) (Index ι) A)
    rw [hshape]
    ext i j
    rcases i with i | i | i <;> rcases j with j | j | j <;>
      simp [matrix, upperBlockMatrix, Matrix.fromBlocks, x, vector, scalar, hrow]

end Parameters

/-- The diagonal coefficients of the hyperbolic scaling matrix. -/
def diagonalWeight (r : Aˣ) : Index ι → A :=
  Sum.elim (fun _ => (r : A)) (Sum.elim (fun _ => 1) (fun _ => (↑r⁻¹ : A)))

/-- The diagonal matrix with top coefficient r, identity middle and bottom r⁻¹. -/
def diagonalMatrix (r : Aˣ) : Matrix (Index ι) (Index ι) A :=
  Matrix.diagonal (diagonalWeight r)

@[simp] theorem diagonalMatrix_mul (r s : Aˣ) :
    diagonalMatrix (ι := ι) (r * s) = diagonalMatrix r * diagonalMatrix s := by
  rw [diagonalMatrix, diagonalMatrix, diagonalMatrix, Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  rcases i with i | i | i <;> simp [diagonalWeight, mul_comm]

omit [Fintype ι] in
@[simp] theorem diagonalMatrix_one : diagonalMatrix (ι := ι) (1 : Aˣ) = 1 := by
  rw [diagonalMatrix, ← Matrix.diagonal_one]
  congr 1
  funext i
  rcases i with i | i | i <;> simp [diagonalWeight]

/-- Hyperbolic diagonal scaling as a general-linear homomorphism. -/
def diagonalEmbedding : Aˣ →* Matrix.GeneralLinearGroup (Index ι) A where
  toFun r :=
    { val := diagonalMatrix r
      inv := diagonalMatrix r⁻¹
      val_inv := by rw [← diagonalMatrix_mul, mul_inv_cancel, diagonalMatrix_one]
      inv_val := by rw [← diagonalMatrix_mul, inv_mul_cancel, diagonalMatrix_one] }
  map_one' := Units.ext diagonalMatrix_one
  map_mul' r s := Units.ext (diagonalMatrix_mul r s)

@[simp] theorem diagonalEmbedding_val (r : Aˣ) :
    ((diagonalEmbedding (ι := ι) r) : Matrix (Index ι) (Index ι) A) =
      diagonalMatrix r := rfl

@[simp] theorem diagonalMatrix_det (r : Aˣ) :
    (diagonalMatrix (ι := ι) r).det = 1 := by
  simp [diagonalMatrix, diagonalWeight, Fintype.prod_sum_type]

theorem diagonalMatrix_preservesForm (H : DiagonalForm c ι) (r : Aˣ)
    (hr : c.bar (r : A) = r) : PreservesForm H (diagonalMatrix r) := by
  have hr' : c.bar (↑r⁻¹ : A) = ↑r⁻¹ := by
    have hi := congrArg c.bar r.val_inv
    rw [map_mul, map_one, hr] at hi
    change (r : A) * c.bar (↑r⁻¹ : A) = 1 at hi
    calc
      c.bar (↑r⁻¹ : A) = ↑r⁻¹ * ((r : A) * c.bar (↑r⁻¹ : A)) := by simp
      _ = ↑r⁻¹ := by rw [hi, mul_one]
  unfold PreservesForm
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [conjugateTranspose, gram, diagonalMatrix, diagonalWeight,
      Matrix.fromBlocks, Matrix.mul_apply,
      Matrix.diagonal_apply, hr, hr']

namespace Parameters

variable {H : DiagonalForm c ι}

/-- Diagonal conjugation realizes the intrinsic weight-one/weight-two scaling. -/
theorem matrix_scale (r : Aˣ) (hr : c.bar (r : A) = r) (x : Parameters H) :
    matrix (scale (r : A) hr x) =
      diagonalMatrix r * matrix x * diagonalMatrix r⁻¹ := by
  ext i j
  rcases i with i | i | i <;> rcases j with j | j | j <;>
    simp [matrix, Matrix.fromBlocks, diagonalMatrix, diagonalWeight,
      Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.one_apply, hr] <;> ring

theorem embedding_scale (r : Aˣ) (hr : c.bar (r : A) = r) (x : Parameters H) :
    embedding H (scale (r : A) hr x) =
      diagonalEmbedding r * embedding H x * (diagonalEmbedding r)⁻¹ := by
  apply Units.ext
  exact matrix_scale r hr x

end Parameters
end Langlands.GroupScheme.HermitianRoot
