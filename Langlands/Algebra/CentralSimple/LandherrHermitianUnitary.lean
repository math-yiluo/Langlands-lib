import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-! # Unitary matrices of prescribed determinant for a Hermitian form -/

noncomputable section

namespace Langlands.CentralSimple.Landherr

open Matrix

universe u v

variable {L : Type u} [Field L] {n : Type v} [Fintype n] [DecidableEq n]
  (c : L →+* L) (hcc : ∀ x, c (c x) = x)

/-- The transpose after applying the ring endomorphism `c` entrywise. -/
def ct (M : Matrix n n L) : Matrix n n L := (M.map c)ᵀ

omit [Fintype n] [DecidableEq n] in
@[simp] theorem ct_apply (M : Matrix n n L) (i j : n) : ct c M i j = c (M j i) := rfl

/-- A nonzero matrix has an anisotropic vector for its sesquilinear form when `c` is not the
identity. -/
theorem exists_anisotropic (hc : ∃ b, c b ≠ b) (K : Matrix n n L) (hK0 : K ≠ 0) : ∃ u : n → L, (fun i => c (u i)) ⬝ᵥ (K *ᵥ u) ≠ 0 := by
  by_contra! h
  apply hK0
  obtain ⟨b, hb⟩ := hc
  have hdiag : ∀ i, K i i = 0 := fun i => by
    have := h (Pi.single i 1)
    simpa [Matrix.mulVec_single, dotProduct, Pi.single_apply] using this
  ext i j
  by_cases hij : i = j
  · subst hij; exact hdiag i
  have hsym : ∀ t : L, t * K i j + c t * K j i = 0 := fun t => by
    have hcu : (fun x => c ((Pi.single i (1 : L) + Pi.single j t : n → L) x)) =
        Pi.single i 1 + Pi.single j (c t) := by
      funext x
      simp only [Pi.add_apply, Pi.single_apply]
      split_ifs <;> simp
    have := h (Pi.single i 1 + Pi.single j t)
    rw [hcu, Matrix.mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add,
      single_dotProduct, single_dotProduct, single_dotProduct, single_dotProduct] at this
    simp only [Matrix.mulVec_single, Pi.smul_apply, Matrix.col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, hdiag] at this
    linear_combination this
  have h1 := hsym 1
  have hb' := hsym b
  rw [map_one, one_mul, one_mul] at h1
  have : (b - c b) * K i j = 0 := by linear_combination hb' - c b * h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm hb
  · rw [h, Matrix.zero_apply]

include hcc in
/-- Let `c` be an involution of `L` with `c b ≠ b` for some `b`. For a nonzero
Hermitian matrix `K` and `δ` with `c δ * δ = 1`, some `g` of determinant `δ` satisfies
`g K ct(g) = K`. -/
theorem exists_unitary_det (hc : ∃ b, c b ≠ b) (K : Matrix n n L) (hK : ct c K = K)
    (hK0 : K ≠ 0) (δ : L) (hδ : c δ * δ = 1) :
    ∃ g : Matrix n n L, g * K * ct c g = K ∧ g.det = δ := by
  obtain ⟨u, hu⟩ := exists_anisotropic c hc K hK0
  have hKe : ∀ x y, c (K x y) = K y x := fun x y => by rw [← ct_apply c K y x, hK]
  set cu : n → L := fun i => c (u i) with hcu
  set w : n → L := K *ᵥ u with hw
  set z : n → L := cu ᵥ* K with hz
  set a : L := cu ⬝ᵥ w with ha
  have hcw : ∀ j, c (w j) = z j := fun j => by
    simp only [hw, hz, Matrix.mulVec, Matrix.vecMul, dotProduct, map_sum, map_mul, hKe, hcu]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hca : c a = a := by
    simp only [ha, dotProduct, map_sum, map_mul, hcw, hcu, hcc]
    simp only [hz, hw, Matrix.mulVec, Matrix.vecMul, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => by ring
  have hza : z ⬝ᵥ u = a := by rw [hz, ha, hw, ← Matrix.dotProduct_mulVec]
  set s : L := (δ - 1) * a⁻¹ with hs
  have hcs : c s = (c δ - 1) * a⁻¹ := by
    rw [hs, map_mul, map_sub, map_one, map_inv₀, hca]
  refine ⟨1 + vecMulVec (s • w) cu, ?_, ?_⟩
  · have hct : ct c (1 + vecMulVec (s • w) cu) = 1 + c s • vecMulVec u z := by
      ext i j
      simp only [ct_apply, Matrix.add_apply, vecMulVec_apply, Pi.smul_apply,
        smul_eq_mul, map_add, map_mul, hcw, hcu, hcc, Matrix.smul_apply]
      by_cases hij : i = j
      · subst hij; simp only [Matrix.one_apply_eq, map_one]; ring
      · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (Ne.symm hij), map_zero]; ring
    rw [hct]
    have e1 : vecMulVec (s • w) cu * K = s • vecMulVec w z := by
      rw [vecMulVec_mul, smul_vecMulVec]
    have e2 : K * vecMulVec u z = vecMulVec w z := by rw [mul_vecMulVec]
    have e3 : vecMulVec w z * vecMulVec u z = a • vecMulVec w z := by
      rw [vecMulVec_mul_vecMulVec, hza, vecMulVec_smul]
    have hcoef : s + c s + c s * (s * a) = 0 := by
      rw [hcs, hs]
      field_simp
      linear_combination hδ
    calc (1 + vecMulVec (s • w) cu) * K * (1 + c s • vecMulVec u z)
        = K + vecMulVec (s • w) cu * K + c s • (K * vecMulVec u z) +
            c s • (vecMulVec (s • w) cu * K * vecMulVec u z) := by
          simp only [add_mul, mul_add, one_mul, mul_one, Matrix.mul_smul]
          abel
      _ = K + (s + c s + c s * (s * a)) • vecMulVec w z := by
          rw [e1, e2, Matrix.smul_mul, e3]
          module
      _ = K := by rw [hcoef, zero_smul, add_zero]
  · rw [Matrix.vecMulVec_eq Unit, Matrix.det_one_add_replicateCol_mul_replicateRow]
    rw [dotProduct_smul, ← ha, smul_eq_mul, hs, mul_assoc, inv_mul_cancel₀ hu, mul_one]
    ring

end Langlands.CentralSimple.Landherr
