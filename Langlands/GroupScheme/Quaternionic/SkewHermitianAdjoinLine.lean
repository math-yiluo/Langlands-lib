import Langlands.GroupScheme.Quaternionic.ScalarQuadratic
import Mathlib.Algebra.Group.Pi.Units
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Matrix.Block

/-! # Adjoining a line to a skew-hermitian Gram matrix -/

noncomputable section

universe u v

open Matrix

namespace Langlands.GroupScheme.Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1700000

section Matrix

variable {A : Type v} [Ring A] {n : ℕ}

/-- Append a one-dimensional diagonal block in the last row and column. -/
def adjoinSkewLine (H : Matrix (Fin n) (Fin n) A) (c : A) : Matrix (Fin (n + 1)) (Fin (n + 1)) A :=
  Matrix.reindexRingEquiv A finSumFinEquiv
    (Matrix.fromBlocks H 0 0 (Matrix.diagonal (fun _ : Fin 1 => c)))

private theorem lineIndex_symm_last : (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).symm (Fin.last n) = .inr 0 := by
  apply (finSumFinEquiv : Fin n ⊕ Fin 1 ≃ Fin (n + 1)).injective
  rw [Equiv.apply_symm_apply]
  rfl

@[simp]
theorem adjoinSkewLine_castSucc (H : Matrix (Fin n) (Fin n) A) (c : A) (i j : Fin n) :
    adjoinSkewLine H c i.castSucc j.castSucc = H i j := by
  change Matrix.fromBlocks H 0 0 (Matrix.diagonal (fun _ : Fin 1 => c))
    (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.castAdd 1 j)) = _
  rw [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_castAdd, Matrix.fromBlocks_apply₁₁]

@[simp]
theorem adjoinSkewLine_castSucc_last (H : Matrix (Fin n) (Fin n) A) (c : A) (i : Fin n) :
    adjoinSkewLine H c i.castSucc (Fin.last n) = 0 := by
  change Matrix.fromBlocks H 0 0 (Matrix.diagonal (fun _ : Fin 1 => c))
    (finSumFinEquiv.symm (Fin.castAdd 1 i)) (finSumFinEquiv.symm (Fin.last n)) = _
  rw [finSumFinEquiv_symm_apply_castAdd, lineIndex_symm_last, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

@[simp]
theorem adjoinSkewLine_last_castSucc (H : Matrix (Fin n) (Fin n) A) (c : A) (i : Fin n) :
    adjoinSkewLine H c (Fin.last n) i.castSucc = 0 := by
  change Matrix.fromBlocks H 0 0 (Matrix.diagonal (fun _ : Fin 1 => c))
    (finSumFinEquiv.symm (Fin.last n)) (finSumFinEquiv.symm (Fin.castAdd 1 i)) = _
  rw [finSumFinEquiv_symm_apply_castAdd, lineIndex_symm_last, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]

@[simp]
theorem adjoinSkewLine_last (H : Matrix (Fin n) (Fin n) A) (c : A) :
    adjoinSkewLine H c (Fin.last n) (Fin.last n) = c := by
  change Matrix.fromBlocks H 0 0 (Matrix.diagonal (fun _ : Fin 1 => c))
    (finSumFinEquiv.symm (Fin.last n)) (finSumFinEquiv.symm (Fin.last n)) = _
  rw [lineIndex_symm_last, Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply_eq]

/-- Coefficient maps commute with adjoining the line. -/
theorem map_adjoinSkewLine {A' : Type*} [Ring A'] (f : A →+* A')
    (H : Matrix (Fin n) (Fin n) A) (c : A) :
    (adjoinSkewLine H c).map f = adjoinSkewLine (H.map f) (f c) := by
  ext i j
  refine Fin.lastCases ?_ (fun i => ?_) i
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  · refine Fin.lastCases ?_ (fun j => ?_) j <;> simp

/-- Adjoining a unit line preserves invertibility. -/
theorem adjoinSkewLine_isUnit {H : Matrix (Fin n) (Fin n) A} (hH : IsUnit H)
    {c : A} (hc : IsUnit c) : IsUnit (adjoinSkewLine H c) := by
  let d : Matrix (Fin 1) (Fin 1) A := Matrix.diagonal (fun _ => c)
  have hd : IsUnit d := (Pi.isUnit_iff.mpr (fun _ : Fin 1 => hc)).map (Matrix.diagonalRingHom (Fin 1) A)
  let M := Matrix.fromBlocks H 0 0 d
  let N := Matrix.fromBlocks (↑hH.unit⁻¹ : Matrix (Fin n) (Fin n) A) 0 0
    (↑hd.unit⁻¹ : Matrix (Fin 1) (Fin 1) A)
  have hMN : M * N = 1 := by
    simp only [M, N, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add,
      add_zero, hH.mul_val_inv, hd.mul_val_inv, Matrix.fromBlocks_one]
  have hNM : N * M = 1 := by
    simp only [M, N, Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, zero_add,
      add_zero, hH.val_inv_mul, hd.val_inv_mul, Matrix.fromBlocks_one]
  exact (show IsUnit M from ⟨⟨M, N, hMN, hNM⟩, rfl⟩).map (Matrix.reindexRingEquiv A finSumFinEquiv)

end Matrix

namespace FirstKindInvolution

variable {F : Type u} {A : Type v} [Field F] [Ring A] [Algebra F A] {n : ℕ}
  (τ : FirstKindInvolution F A)

/-- The Gram evaluation splits into the old row and the last coordinate. -/
theorem matrixSesqBilin_adjoinSkewLine (H : Matrix (Fin n) (Fin n) A) (c : A)
    (x y : Fin (n + 1) → A) :
    τ.matrixSesqBilin (adjoinSkewLine H c) x y =
      τ.matrixSesqBilin H (x ∘ Fin.castSucc) (y ∘ Fin.castSucc) +
        x (Fin.last n) * c * τ (y (Fin.last n)) := by
  simp only [matrixSesqBilin_apply, Fin.sum_univ_castSucc, adjoinSkewLine_castSucc,
    adjoinSkewLine_castSucc_last, adjoinSkewLine_last_castSucc, adjoinSkewLine_last, mul_zero,
    zero_mul, add_zero, Finset.sum_const_zero, zero_add, Function.comp_apply]

/-- A skew line adjoined to an antihermitian matrix is antihermitian. -/
theorem IsAntihermitian.adjoinSkewLine {D : Type v} [DivisionRing D] [Algebra F D]
    {σ : FirstKindInvolution F D} {H : Matrix (Fin n) (Fin n) D} (hH : σ.IsAntihermitian H)
    {c : D} (hc : c ∈ σ.alternatingSubspace) : σ.IsAntihermitian (adjoinSkewLine H c) := by
  have hskew : σ c = -c := by
    obtain ⟨a, rfl⟩ := σ.mem_alternatingSubspace.mp hc
    rw [σ.map_sub, σ.apply_apply, neg_sub]
  constructor
  · ext i j
    rw [FirstKindInvolution.matrix_apply, Matrix.neg_apply]
    refine Fin.lastCases ?_ (fun i => ?_) i
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simpa only [adjoinSkewLine_last] using hskew
      · rw [adjoinSkewLine_castSucc_last, adjoinSkewLine_last_castSucc, σ.map_zero, neg_zero]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · rw [adjoinSkewLine_last_castSucc, adjoinSkewLine_castSucc_last, σ.map_zero, neg_zero]
      · simpa only [adjoinSkewLine_castSucc, FirstKindInvolution.matrix_apply, Matrix.neg_apply]
          using congrArg (fun M : Matrix (Fin n) (Fin n) D => M i j) hH.1
  · intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · simpa only [adjoinSkewLine_last] using hc
    · simpa only [adjoinSkewLine_castSucc] using hH.2 i

end FirstKindInvolution

end Langlands.GroupScheme.Quaternionic
