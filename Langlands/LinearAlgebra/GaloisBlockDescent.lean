import Langlands.LinearAlgebra.GaloisVectorDescent
import Mathlib.Data.Matrix.Block

/-! # Blockwise Hilbert 90 for matrix cocycles -/

noncomputable section

universe u v w

namespace Langlands.LinearAlgebra.GaloisBlockDescent

open Matrix Langlands.LinearAlgebra.GaloisVectorDescent

variable {k L : Type u} [Field k] [Field L] [Algebra k L]
variable (H : Subgroup (L ≃ₐ[k] L)) [Finite H]

section Sigma

variable {o : Type v} [Fintype o] [DecidableEq o] {m : o → Type w}
  [∀ b, Fintype (m b)] [∀ b, DecidableEq (m b)]

/-- Hilbert 90 for a family of matrix cocycles, assembled into one block-diagonal
invertible matrix. -/
theorem exists_blockDiagonal'_coboundary (c : H → ∀ b, Matrix (m b) (m b) L)
    (hc1 : ∀ b, c 1 b = 1)
    (hc : ∀ σ τ b, c (σ * τ) b = c σ b * (c τ b).map σ.val) :
    ∃ (P : ∀ b, GL (m b) L) (Q : GL (Σ b, m b) L),
      (Q : Matrix (Σ b, m b) (Σ b, m b) L) =
          blockDiagonal' (fun b => (P b : Matrix (m b) (m b) L)) ∧
        ∀ σ, blockDiagonal' (c σ) * (Q : Matrix (Σ b, m b) (Σ b, m b) L).map σ.val = Q := by
  let P : ∀ b, GL (m b) L := fun b =>
    coboundaryMatrix H (fun σ => c σ b) (hc1 b) (fun σ τ => hc σ τ b)
  let Q : GL (Σ b, m b) L :=
    ⟨blockDiagonal' (fun b => (P b : Matrix (m b) (m b) L)),
      blockDiagonal' (fun b => (((P b)⁻¹ : GL (m b) L) : Matrix (m b) (m b) L)),
      by rw [← blockDiagonal'_mul]; simp only [Units.mul_inv]; exact blockDiagonal'_one,
      by rw [← blockDiagonal'_mul]; simp only [Units.inv_mul]; exact blockDiagonal'_one⟩
  have hQ : (Q : Matrix (Σ b, m b) (Σ b, m b) L) =
      blockDiagonal' (fun b => (P b : Matrix (m b) (m b) L)) := rfl
  refine ⟨P, Q, hQ, fun σ => ?_⟩
  rw [hQ, blockDiagonal'_map _ _ (map_zero σ.val), ← blockDiagonal'_mul]
  congr 1
  funext b
  exact coboundaryMatrix_spec H (fun σ => c σ b) (hc1 b) (fun σ τ => hc σ τ b) σ

end Sigma

variable {I : Type w} [Fintype I] [DecidableEq I] {B : Type v}

/-- Blockwise Hilbert 90: a matrix cocycle of a finite automorphism group whose
values have zero entries between indices with different labels is trivialised by an
invertible matrix with the same block shape. -/
theorem exists_blockwise_matrix_coboundary (w : I → B) (c : H → Matrix I I L)
    (hc1 : c 1 = 1) (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val)
    (hblock : ∀ σ i j, w i ≠ w j → c σ i j = 0) :
    ∃ P : GL I L, (∀ σ, c σ * (P : Matrix I I L).map σ.val = P) ∧
      ∀ i j, w i ≠ w j → (P : Matrix I I L) i j = 0 := by
  classical
  let w' : I → Set.range w := Set.rangeFactorization w
  have hw' (i j : I) (h : w i ≠ w j) : w' i ≠ w' j := fun h' => h (congrArg Subtype.val h')
  let e := Equiv.sigmaFiberEquiv w'
  have he (i : I) : e.symm i = ⟨w' i, i, rfl⟩ := rfl
  let blk : H → ∀ b : Set.range w, Matrix {i // w' i = b} {i // w' i = b} L :=
    fun σ b i j => c σ i.1 j.1
  have hdiag (σ : H) : (c σ).submatrix e e = blockDiagonal' (blk σ) := by
    ext ⟨b, i⟩ ⟨b', j⟩
    by_cases h : b = b'
    · subst h
      rw [blockDiagonal'_apply_eq]
      rfl
    · rw [blockDiagonal'_apply_ne _ _ _ h]
      apply hblock
      intro h'
      apply h
      rw [← i.2, ← j.2]
      exact Subtype.ext h'
  have hblk1 (b : Set.range w) : blk 1 b = 1 := by
    ext i j
    simp only [blk, hc1, one_apply, Subtype.ext_iff]
  have hblkc (σ τ : H) (b : Set.range w) : blk (σ * τ) b = blk σ b * (blk τ b).map σ.val := by
    have h : (c (σ * τ)).submatrix e e = (c σ * (c τ).map σ.val).submatrix e e := by
      rw [hc σ τ]
    rw [← submatrix_mul_equiv _ _ e e e, hdiag, hdiag, submatrix_map, hdiag,
      blockDiagonal'_map _ _ (map_zero σ.val), ← blockDiagonal'_mul] at h
    exact congrFun (blockDiagonal'_injective h) b
  obtain ⟨P, Q, hQ, hQc⟩ := exists_blockDiagonal'_coboundary H blk hblk1 hblkc
  have hinj (M N : Matrix I I L) (h : M.submatrix e e = N.submatrix e e) : M = N := by
    have h2 := congrArg (fun X : Matrix _ _ L => X.submatrix e.symm e.symm) h
    simpa only [submatrix_submatrix, Equiv.self_comp_symm, submatrix_id_id] using h2
  let R : GL I L :=
    ⟨(Q : Matrix _ _ L).submatrix e.symm e.symm,
      ((Q⁻¹ : GL _ L) : Matrix _ _ L).submatrix e.symm e.symm,
      by rw [submatrix_mul_equiv, Units.mul_inv, submatrix_one_equiv],
      by rw [submatrix_mul_equiv, Units.inv_mul, submatrix_one_equiv]⟩
  have hR : (R : Matrix I I L) = (Q : Matrix _ _ L).submatrix e.symm e.symm := rfl
  have hRe : (R : Matrix I I L).submatrix e e = Q := by
    rw [hR, submatrix_submatrix, Equiv.symm_comp_self, submatrix_id_id]
  refine ⟨R, fun σ => ?_, fun i j hij => ?_⟩
  · apply hinj
    rw [← submatrix_mul_equiv _ _ e e e, hdiag, submatrix_map, hRe]
    exact hQc σ
  · rw [hR, submatrix_apply, he, he, hQ]
    exact blockDiagonal'_apply_ne _ _ _ (hw' i j hij)

/-- A chosen invertible matrix with the block shape of `w` trivialising a
block-shaped matrix cocycle, as provided by `exists_blockwise_matrix_coboundary`. -/
def blockCoboundaryMatrix (w : I → B) (c : H → Matrix I I L)
    (hc1 : c 1 = 1) (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val)
    (hblock : ∀ σ i j, w i ≠ w j → c σ i j = 0) : GL I L :=
  Classical.choose (exists_blockwise_matrix_coboundary H w c hc1 hc hblock)

/-- The chosen block-shaped matrix satisfies `c σ * σ(P) = P`. -/
theorem blockCoboundaryMatrix_spec (w : I → B) (c : H → Matrix I I L)
    (hc1 : c 1 = 1) (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val)
    (hblock : ∀ σ i j, w i ≠ w j → c σ i j = 0) (σ : H) :
    c σ * (blockCoboundaryMatrix H w c hc1 hc hblock : Matrix I I L).map σ.val =
      blockCoboundaryMatrix H w c hc1 hc hblock :=
  (Classical.choose_spec (exists_blockwise_matrix_coboundary H w c hc1 hc hblock)).1 σ

/-- The chosen matrix has zero entries between indices with different labels. -/
theorem blockCoboundaryMatrix_apply_of_ne (w : I → B) (c : H → Matrix I I L)
    (hc1 : c 1 = 1) (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val)
    (hblock : ∀ σ i j, w i ≠ w j → c σ i j = 0) {i j : I} (hij : w i ≠ w j) :
    (blockCoboundaryMatrix H w c hc1 hc hblock : Matrix I I L) i j = 0 :=
  (Classical.choose_spec (exists_blockwise_matrix_coboundary H w c hc1 hc hblock)).2 i j hij

/-- The cocycle is the coboundary `c σ = P * σ(P⁻¹)` of the chosen block-shaped
matrix. -/
theorem eq_blockCoboundaryMatrix_mul (w : I → B) (c : H → Matrix I I L)
    (hc1 : c 1 = 1) (hc : ∀ σ τ, c (σ * τ) = c σ * (c τ).map σ.val)
    (hblock : ∀ σ i j, w i ≠ w j → c σ i j = 0) (σ : H) :
    c σ = (blockCoboundaryMatrix H w c hc1 hc hblock : Matrix I I L) *
      (((blockCoboundaryMatrix H w c hc1 hc hblock)⁻¹ : GL I L) : Matrix I I L).map σ.val :=
  eq_mul_map_inv_of_mul_map_eq σ.val _ (blockCoboundaryMatrix_spec H w c hc1 hc hblock σ)

/-- Blockwise Hilbert 90 for `GL`-valued cocycles: a cocycle
`c (σ * τ) = c σ * σ(c τ)` whose values have zero entries between indices with
different labels is trivialised, `c σ * σ(P) = P`, by some `P` with the same block
shape. -/
theorem exists_blockwise_coboundary (w : I → B) (c : H → GL I L) (hc1 : c 1 = 1)
    (hc : ∀ σ τ,
      c (σ * τ) = c σ * Matrix.GeneralLinearGroup.map (σ.val : L →+* L) (c τ))
    (hblock : ∀ σ i j, w i ≠ w j → c σ i j = 0) :
    ∃ P : GL I L,
      (∀ σ, c σ * Matrix.GeneralLinearGroup.map (σ.val : L →+* L) P = P) ∧
        ∀ i j, w i ≠ w j → P i j = 0 := by
  have hmap (σ : H) (g : GL I L) :
      ((Matrix.GeneralLinearGroup.map (σ.val : L →+* L) g : GL I L) : Matrix I I L) =
        (g : Matrix I I L).map σ.val := rfl
  have hc1' : (fun σ => (c σ : Matrix I I L)) 1 = 1 := by
    simp only [hc1, Units.val_one]
  have hc' : ∀ σ τ, (fun σ => (c σ : Matrix I I L)) (σ * τ) =
      (fun σ => (c σ : Matrix I I L)) σ * ((fun σ => (c σ : Matrix I I L)) τ).map σ.val := by
    intro σ τ
    simp only
    rw [hc σ τ, Units.val_mul, hmap]
  obtain ⟨P, hP, hPb⟩ := exists_blockwise_matrix_coboundary H w _ hc1' hc' hblock
  refine ⟨P, fun σ => Units.ext ?_, hPb⟩
  rw [Units.val_mul, hmap]
  exact hP σ

end Langlands.LinearAlgebra.GaloisBlockDescent
