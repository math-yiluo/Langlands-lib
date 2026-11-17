import Langlands.Global.RankinSelberg.RectangularIwasawaMinors
import Langlands.Group.GL.CartanProof
import Langlands.LinearAlgebra.TriangularUnitary

/-! # Local bounds from rectangular trailing minors -/

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.GeneralLinear.RectangularIwasawa

/-- The product of the diagonal entries in a trailing square block. -/
def trailingDiagonalProduct {R : Type u} [CommRing R] (a d : ℕ)
    (B : Matrix (Fin (a + d)) (Fin (a + d)) R) : R :=
  ∏ i : Fin d, B (i.natAdd a) (i.natAdd a)

section Valuation

variable {F : Type u} [Field F] {Γ₀ : Type v} [LinearOrderedCommGroupWithZero Γ₀]
    (w : Valuation F Γ₀) {a d : ℕ}

/-- An integral right factor bounds every trailing minor by the trailing
diagonal product of an upper triangular left factor, with constant one. -/
theorem valuation_trailing_minor_le
    (B K : Matrix (Fin (a + d)) (Fin (a + d)) F)
    (hB : B.IsUpperTriangular) (hK : ∀ i j, K i j ∈ w.integer)
    (c : Fin d → Fin (a + d)) :
    w (((B * K).submatrix (Fin.natAdd a) c).det) ≤
      w (trailingDiagonalProduct a d B) := by
  rw [det_trailing_submatrix_mul B K hB c, map_mul]
  apply mul_le_of_le_of_le_one le_rfl
  apply (w.mem_integer_iff _).mp
  exact Cartan.det_mem_integer (K.submatrix (Fin.natAdd a) c)
    (fun i j => hK _ _)

/-- In a rectangular Iwasawa factorization, each rectangular coordinate is
bounded by the trailing diagonal product, with constant one. -/
theorem valuation_lowerBlockPair_coordinate_le
    (g : Langlands.GeneralLinear a F) (x : Matrix (Fin d) (Fin a) F)
    (B K : Matrix (Fin (a + d)) (Fin (a + d)) F)
    (hB : B.IsUpperTriangular) (hK : ∀ i j, K i j ∈ w.integer)
    (hg : (lowerBlockPair g x 1).val = B * K) (i : Fin d) (j : Fin a) :
    w (x i j) ≤ w (trailingDiagonalProduct a d B) := by
  have hh := valuation_trailing_minor_le w B K hB hK (coordinateMinorColumns a d i j)
  rwa [← hg, lowerBlockPair_coordinate_minor] at hh

/-- The same trailing diagonal product is at least one. -/
theorem one_le_valuation_lowerBlockPair_trailingDiagonalProduct
    (g : Langlands.GeneralLinear a F) (x : Matrix (Fin d) (Fin a) F)
    (B K : Matrix (Fin (a + d)) (Fin (a + d)) F)
    (hB : B.IsUpperTriangular) (hK : ∀ i j, K i j ∈ w.integer)
    (hg : (lowerBlockPair g x 1).val = B * K) :
    1 ≤ w (trailingDiagonalProduct a d B) := by
  have hh := valuation_trailing_minor_le w B K hB hK (Fin.natAdd a)
  rwa [← hg, lowerBlockPair_trailing_minor, map_one] at hh

/-- A trailing diagonal product at most one forces integral rectangular
coordinates. -/
theorem lowerBlockPair_coordinate_mem_integer
    (g : Langlands.GeneralLinear a F) (x : Matrix (Fin d) (Fin a) F)
    (B K : Matrix (Fin (a + d)) (Fin (a + d)) F)
    (hB : B.IsUpperTriangular) (hK : ∀ i j, K i j ∈ w.integer)
    (hg : (lowerBlockPair g x 1).val = B * K)
    (hprod : w (trailingDiagonalProduct a d B) ≤ 1) (i : Fin d) (j : Fin a) :
    x i j ∈ w.integer :=
  (w.mem_integer_iff _).mpr
    ((valuation_lowerBlockPair_coordinate_le w g x B K hB hK hg i j).trans hprod)

end Valuation

section Norm

variable {𝕜 : Type u} [NormedField 𝕜] {a d : ℕ}

/-- The Leibniz formula bounds the determinant of a matrix whose entries
have norm at most one by the factorial of its rank. -/
theorem norm_det_le_factorial (M : Matrix (Fin d) (Fin d) 𝕜)
    (hM : ∀ i j, ‖M i j‖ ≤ 1) :
    ‖M.det‖ ≤ (d.factorial : ℝ) := by
  classical
  rw [Matrix.det_apply']
  calc
    _ ≤ ∑ σ : Equiv.Perm (Fin d), ‖((Equiv.Perm.sign σ : ℤ) : 𝕜) *
        ∏ i, M (σ i) i‖ := norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin d), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro σ _
      have hp : ‖∏ i : Fin d, M (σ i) i‖ ≤ 1 := by
        rw [norm_prod]
        exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => hM _ _)
      rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;>
        simpa [hs] using hp
    _ = (d.factorial : ℝ) := by simp [Fintype.card_perm]

/-- A right factor with entries of norm at most one bounds trailing minors
by `d!` times the norm of the trailing diagonal product. -/
theorem norm_trailing_minor_le
    (B K : Matrix (Fin (a + d)) (Fin (a + d)) 𝕜)
    (hB : B.IsUpperTriangular) (hK : ∀ i j, ‖K i j‖ ≤ 1)
    (c : Fin d → Fin (a + d)) :
    ‖((B * K).submatrix (Fin.natAdd a) c).det‖ ≤
      ‖trailingDiagonalProduct a d B‖ * (d.factorial : ℝ) := by
  rw [det_trailing_submatrix_mul B K hB c, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_det_le_factorial (K.submatrix (Fin.natAdd a) c) (fun i j => hK _ _))
    (norm_nonneg _)

/-- Norm bounds on the right factor give polynomial control of every
rectangular coordinate by the trailing diagonal product. -/
theorem norm_lowerBlockPair_coordinate_le
    (g : Langlands.GeneralLinear a 𝕜) (x : Matrix (Fin d) (Fin a) 𝕜)
    (B K : Matrix (Fin (a + d)) (Fin (a + d)) 𝕜)
    (hB : B.IsUpperTriangular) (hK : ∀ i j, ‖K i j‖ ≤ 1)
    (hg : (lowerBlockPair g x 1).val = B * K) (i : Fin d) (j : Fin a) :
    ‖x i j‖ ≤ ‖trailingDiagonalProduct a d B‖ * (d.factorial : ℝ) := by
  have hh := norm_trailing_minor_le B K hB hK (coordinateMinorColumns a d i j)
  rwa [← hg, lowerBlockPair_coordinate_minor] at hh

/-- The principal trailing minor gives the corresponding lower bound. -/
theorem one_le_norm_lowerBlockPair_trailingDiagonalProduct
    (g : Langlands.GeneralLinear a 𝕜) (x : Matrix (Fin d) (Fin a) 𝕜)
    (B K : Matrix (Fin (a + d)) (Fin (a + d)) 𝕜)
    (hB : B.IsUpperTriangular) (hK : ∀ i j, ‖K i j‖ ≤ 1)
    (hg : (lowerBlockPair g x 1).val = B * K) :
    1 ≤ ‖trailingDiagonalProduct a d B‖ * (d.factorial : ℝ) := by
  have hh := norm_trailing_minor_le B K hB hK (Fin.natAdd a)
  rwa [← hg, lowerBlockPair_trailing_minor, norm_one] at hh

end Norm

section Unitary

variable {𝕜 : Type u} [RCLike 𝕜] {a d : ℕ}

/-- In the archimedean Iwasawa case, a unitary right factor supplies the
required bound on its entries. -/
theorem norm_lowerBlockPair_coordinate_le_of_unitary
    (g : Langlands.GeneralLinear a 𝕜) (x : Matrix (Fin d) (Fin a) 𝕜)
    (B K : Matrix (Fin (a + d)) (Fin (a + d)) 𝕜)
    (hB : B.IsUpperTriangular) (hK : K ∈ Matrix.unitaryGroup (Fin (a + d)) 𝕜)
    (hg : (lowerBlockPair g x 1).val = B * K) (i : Fin d) (j : Fin a) :
    ‖x i j‖ ≤ ‖trailingDiagonalProduct a d B‖ * (d.factorial : ℝ) :=
  norm_lowerBlockPair_coordinate_le g x B K hB
    (Langlands.LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup hK) hg i j

end Unitary

end Langlands.GeneralLinear.RectangularIwasawa
