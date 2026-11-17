import Langlands.Global.RankinSelberg.RectangularRootBounds
import Langlands.Group.GL.LowerTriangularBlockCoordinates

/-! # Diagonal corrections independent of the leading torus -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularIwasawa

open Langlands.Global.PrimitiveAdelicHeight

variable {R : Type u} [CommRing R] {a d n : ℕ}

/-- Pad a unit diagonal tuple by ones on the trailing coordinates. -/
def paddedDiagonal (d : ℕ) (b : Fin a → Rˣ) : Fin (a + d) → Rˣ :=
  Fin.append b (fun _ => 1)

theorem diagonalGL_paddedDiagonal (b : Fin a → Rˣ) :
    diagonalGL (paddedDiagonal d b) = lowerBlockPair (diagonalGL b) 0 1 := by
  apply Units.ext
  ext i j
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j => simp [diagonalGL, paddedDiagonal, Matrix.diagonal_apply]
    | right j =>
      have hne : i.castAdd d ≠ j.natAdd a := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      simp [diagonalGL, paddedDiagonal, hne]
  | right i =>
    induction j using Fin.addCases with
    | left j =>
      have hne : i.natAdd a ≠ j.castAdd d := by
        intro he
        have hv := congrArg Fin.val he
        simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
        omega
      simp [diagonalGL, hne]
    | right j => simp [diagonalGL, paddedDiagonal, Matrix.diagonal_apply, Matrix.one_apply]

theorem diagonalGL_mul (b c : Fin n → Rˣ) :
    diagonalGL (fun i => b i * c i) = diagonalGL b * diagonalGL c := by
  apply Units.ext
  change Matrix.diagonal (fun i => ((b i * c i : Rˣ) : R)) =
    Matrix.diagonal (fun i => (b i : R)) * Matrix.diagonal (fun i => (c i : R))
  rw [Matrix.diagonal_mul_diagonal]
  rfl

/-- The rectangular matrix with diagonal leading block is the padded
diagonal times a lower unipotent matrix independent of that block. -/
theorem lowerBlockPair_diagonal_eq_mul
    (b : Fin a → Rˣ) (x : Matrix (Fin d) (Fin a) R) :
    lowerBlockPair (diagonalGL b) x 1 =
      diagonalGL (paddedDiagonal d b) * lowerBlockPair 1 x 1 := by
  rw [diagonalGL_paddedDiagonal, lowerBlockPair_mul_lowerBlockPair]
  simp

/-- An Iwasawa factorization of the lower unipotent gives factorizations
for every leading diagonal using the same compact factor and correction. -/
theorem lowerBlockPair_diagonal_factorization
    (x : Matrix (Fin d) (Fin a) R) (U K : Langlands.GeneralLinear (a + d) R)
    (c : Fin (a + d) → Rˣ) (hU : IsUnitriangular U.val)
    (hfac : lowerBlockPair 1 x 1 = U * diagonalGL c * K)
    (b : Fin a → Rˣ) :
    ∃ V : Langlands.GeneralLinear (a + d) R, IsUnitriangular V.val ∧
      lowerBlockPair (diagonalGL b) x 1 =
        V * diagonalGL (fun i => paddedDiagonal d b i * c i) * K := by
  let D := diagonalGL (paddedDiagonal d b)
  refine ⟨D * U * D⁻¹, ?_, ?_⟩
  · exact hU.diagonal_conj (paddedDiagonal d b)
  · rw [lowerBlockPair_diagonal_eq_mul, hfac, diagonalGL_mul]
    change D * (U * diagonalGL c * K) =
      (D * U * D⁻¹) * (D * diagonalGL c) * K
    group

/-- The inverse lower unipotent is obtained by negating the rectangle. -/
theorem lowerBlockPair_one_inv (x : Matrix (Fin d) (Fin a) R) :
    (lowerBlockPair (1 : Langlands.GeneralLinear a R) x 1)⁻¹ =
      lowerBlockPair 1 (-x) 1 := by
  rw [lowerBlockPair_inv]
  simp

section Norm

variable {𝕜 : Type u} [NormedField 𝕜]

/-- Entry bounds on a rectangle control all entries of its lower unipotent
matrix. -/
theorem norm_lowerBlockPair_one_entry_le
    (x : Matrix (Fin d) (Fin a) 𝕜) (C : ℝ) (hC : 1 ≤ C)
    (hx : ∀ i j, ‖x i j‖ ≤ C) (i j : Fin (a + d)) :
    ‖lowerBlockPair (1 : Langlands.GeneralLinear a 𝕜) x 1 i j‖ ≤ C := by
  induction i using Fin.addCases with
  | left i =>
    induction j using Fin.addCases with
    | left j =>
      rw [lowerBlockPair_11]
      exact (norm_map_one_le (RingHom.id 𝕜) i j).trans hC
    | right j =>
      rw [lowerBlockPair_12, norm_zero]
      exact zero_le_one.trans hC
  | right i =>
    induction j using Fin.addCases with
    | left j => simpa only [lowerBlockPair_21] using hx i j
    | right j =>
      rw [lowerBlockPair_22]
      exact (norm_map_one_le (RingHom.id 𝕜) i j).trans hC

/-- The same entry bound controls the inverse lower unipotent. -/
theorem norm_lowerBlockPair_one_inv_entry_le
    (x : Matrix (Fin d) (Fin a) 𝕜) (C : ℝ) (hC : 1 ≤ C)
    (hx : ∀ i j, ‖x i j‖ ≤ C) (i j : Fin (a + d)) :
    ‖(lowerBlockPair (1 : Langlands.GeneralLinear a 𝕜) x 1)⁻¹ i j‖ ≤ C := by
  rw [lowerBlockPair_one_inv]
  exact norm_lowerBlockPair_one_entry_le (-x) C hC (by simpa using hx) i j

/-- Multiplying by the right factor and its inverse bounds the diagonal
correction in both directions, without a determinant estimate. -/
theorem norm_factor_entries_le
    (M B K : Langlands.GeneralLinear n 𝕜) (hfac : M = B * K)
    (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i j, ‖M i j‖ ≤ C) (hMinv : ∀ i j, ‖M⁻¹ i j‖ ≤ C)
    (hK : ∀ i j, ‖K i j‖ ≤ 1) (hKinv : ∀ i j, ‖K⁻¹ i j‖ ≤ 1)
    (i j : Fin n) :
    ‖B i j‖ ≤ n * C ∧ ‖B⁻¹ i j‖ ≤ n * C := by
  have hB : B = M * K⁻¹ := by rw [hfac]; group
  have hBi : B⁻¹ = K * M⁻¹ := by rw [hfac]; group
  constructor
  · rw [hB]
    exact (norm_map_mul_apply_le (RingHom.id 𝕜) M.val (K⁻¹).val hC hM hKinv i j).trans_eq
      (by simp)
  · rw [hBi]
    exact (norm_map_mul_apply_le (RingHom.id 𝕜) K.val (M⁻¹).val zero_le_one hK hMinv i j).trans_eq
      (by simp)

end Norm

section Ultrametric

variable {𝕜 : Type u} [NormedField 𝕜] [IsUltrametricDist 𝕜]

private theorem norm_mul_entry_le_ultrametric
    (M N : Matrix (Fin n) (Fin n) 𝕜) (C D : ℝ) (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hM : ∀ i j, ‖M i j‖ ≤ C) (hN : ∀ i j, ‖N i j‖ ≤ D) (i j : Fin n) :
    ‖(M * N) i j‖ ≤ C * D := by
  rw [Matrix.mul_apply]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hC hD)
  intro k _
  rw [norm_mul]
  exact mul_le_mul (hM i k) (hN k j) (norm_nonneg _) hC

/-- The ultrametric correction bound keeps constant one, including when
all rectangular coordinates are integral. -/
theorem norm_factor_entries_le_ultrametric
    (M B K : Langlands.GeneralLinear n 𝕜) (hfac : M = B * K)
    (C : ℝ) (hC : 0 ≤ C)
    (hM : ∀ i j, ‖M i j‖ ≤ C) (hMinv : ∀ i j, ‖M⁻¹ i j‖ ≤ C)
    (hK : ∀ i j, ‖K i j‖ ≤ 1) (hKinv : ∀ i j, ‖K⁻¹ i j‖ ≤ 1)
    (i j : Fin n) :
    ‖B i j‖ ≤ C ∧ ‖B⁻¹ i j‖ ≤ C := by
  have hB : B = M * K⁻¹ := by rw [hfac]; group
  have hBi : B⁻¹ = K * M⁻¹ := by rw [hfac]; group
  constructor
  · rw [hB]
    exact (norm_mul_entry_le_ultrametric M.val (K⁻¹).val C 1 hC zero_le_one
      hM hKinv i j).trans_eq (mul_one _)
  · rw [hBi]
    exact (norm_mul_entry_le_ultrametric K.val (M⁻¹).val 1 C zero_le_one hC
      hK hMinv i j).trans_eq (one_mul _)

end Ultrametric

end Langlands.GeneralLinear.RectangularIwasawa
