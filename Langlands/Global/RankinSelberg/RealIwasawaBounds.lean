import Langlands.Global.RankinSelberg.RealIwasawa
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Algebra.Order.Star.Real
import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-! # Bounds for the toral Iwasawa coordinate of `GL_n(ℝ)` -/

noncomputable section

open Matrix

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealIwasawa

open Langlands.Archimedean (unitaryCompact)

variable {n : ℕ}

/-- `k kᵀ = 1` for orthogonal `k`. -/
theorem unitary_mul_transpose (k : unitaryCompact ℝ n) :
    ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) *
      ((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
  rw [← val_inv_of_mem k, ← Units.val_mul, mul_inv_cancel, Units.val_one]

/-- The value of the inverse of the triangular Iwasawa coordinate. -/
theorem bpart_inv_diag (g : Langlands.GeneralLinear n ℝ) (i : Fin n) :
    (((bpart g)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) i i =
      Real.exp (-alpha g i) := by
  have hB := isPosUpper_bpart g
  have hBi := isPosUpper_inv hB
  have h : ((bpart g : Matrix (Fin n) (Fin n) ℝ) *
      (((bpart g)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) i i =
      (1 : Matrix (Fin n) (Fin n) ℝ) i i := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  rw [upper_mul_diag hB.1 hBi.1, Matrix.one_apply_eq] at h
  rw [Real.exp_neg, exp_alpha]
  exact (eq_inv_of_mul_eq_one_right h)

/-- **Row bound.** `exp(2 α_i(g)) ≤ ∑_q g_(iq)²`. -/
theorem exp_two_mul_alpha_le (g : Langlands.GeneralLinear n ℝ) (i : Fin n) :
    Real.exp (2 * alpha g i) ≤ ∑ q, ((g : Matrix (Fin n) (Fin n) ℝ) i q) ^ 2 := by
  set B := ((bpart g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) with hB
  set K := ((kpart g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) with hK
  have hg : (g : Matrix (Fin n) (Fin n) ℝ) = B * K := by
    rw [hB, hK, ← Units.val_mul, bpart_mul_kpart]
  have h1 : ∑ q, ((g : Matrix (Fin n) (Fin n) ℝ) i q) ^ 2 = (B * Bᵀ) i i := by
    have e : ((g : Matrix (Fin n) (Fin n) ℝ) * (g : Matrix (Fin n) (Fin n) ℝ)ᵀ) i i =
        ∑ q, ((g : Matrix (Fin n) (Fin n) ℝ) i q) ^ 2 := by
      simp [Matrix.mul_apply, sq]
    rw [← e, hg, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc K,
      unitary_mul_transpose, Matrix.one_mul]
  have hex : Real.exp (2 * alpha g i) = B i i * B i i := by
    rw [two_mul, Real.exp_add, exp_alpha]
  rw [h1, hex, Matrix.mul_apply]
  refine le_of_eq_of_le (by rw [Matrix.transpose_apply]) (Finset.single_le_sum
    (f := fun p => B i p * Bᵀ p i) (fun p _ => ?_) (Finset.mem_univ i))
  simp only [Matrix.transpose_apply]
  exact mul_self_nonneg _

/-- The inverse of `g` is `kpart(g)ᵀ · bpart(g)⁻¹`. -/
theorem inv_val_eq (g : Langlands.GeneralLinear n ℝ) :
    ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) =
      ((kpart g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)ᵀ *
        (((bpart g)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
  rw [← val_inv_of_mem (kpart g), ← Units.val_mul, ← _root_.mul_inv_rev, bpart_mul_kpart]

/-- **Column bound.** `exp(−2 α_i(g)) ≤ ∑_p ((g⁻¹)_(pi))²`. -/
theorem exp_neg_two_mul_alpha_le (g : Langlands.GeneralLinear n ℝ) (i : Fin n) :
    Real.exp (-(2 * alpha g i)) ≤
      ∑ p, (((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) p i) ^ 2 := by
  set C := (((bpart g)⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) with hC
  set K := ((kpart g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) with hK
  have hg := inv_val_eq g
  rw [← hC, ← hK] at hg
  have h1 : ∑ p, (((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) p i) ^ 2 =
      (Cᵀ * C) i i := by
    have e : ((((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ))ᵀ *
        ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) i i =
        ∑ p, (((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) p i) ^ 2 := by
      simp [Matrix.mul_apply, sq]
    rw [← e, hg, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc K, unitary_mul_transpose, Matrix.one_mul]
  have hex : Real.exp (-(2 * alpha g i)) = C i i * C i i := by
    rw [hC, bpart_inv_diag, ← Real.exp_add]
    ring_nf
  rw [h1, hex, Matrix.mul_apply]
  refine le_of_eq_of_le (by rw [Matrix.transpose_apply]) (Finset.single_le_sum
    (f := fun p => Cᵀ i p * C p i) (fun p _ => ?_) (Finset.mem_univ i))
  simp only [Matrix.transpose_apply]
  exact mul_self_nonneg _

/-- **The Gram determinant of the first columns of `g⁻¹`.** For `g ∈ GL_(a+e)(ℝ)`, let `C` be the
`(a+e) × a` matrix of the first `a` columns of `g⁻¹`. Then `det(ᵗC C) = exp(−2 ∑_(j<a) α_j(g))`. -/
theorem det_gram_inv_cols {a e : ℕ} (g : Langlands.GeneralLinear (a + e) ℝ) :
    Matrix.det ((((g⁻¹ : Langlands.GeneralLinear (a + e) ℝ) :
        Matrix (Fin (a + e)) (Fin (a + e)) ℝ).submatrix id (Fin.castAdd e))ᵀ *
      (((g⁻¹ : Langlands.GeneralLinear (a + e) ℝ) :
        Matrix (Fin (a + e)) (Fin (a + e)) ℝ).submatrix id (Fin.castAdd e))) =
      Real.exp (-(2 * ∑ j : Fin a, alpha g (Fin.castAdd e j))) := by
  set C := (((bpart g)⁻¹ : Langlands.GeneralLinear (a + e) ℝ) :
    Matrix (Fin (a + e)) (Fin (a + e)) ℝ) with hC
  set K := ((kpart g : Langlands.GeneralLinear (a + e) ℝ) :
    Matrix (Fin (a + e)) (Fin (a + e)) ℝ) with hK
  have hCu : C.IsUpperTriangular := (isPosUpper_inv (isPosUpper_bpart g)).1
  have hg := inv_val_eq g
  rw [← hC, ← hK] at hg
  set T : Matrix (Fin a) (Fin a) ℝ := C.submatrix (Fin.castAdd e) (Fin.castAdd e) with hT
  have hsub : ((g⁻¹ : Langlands.GeneralLinear (a + e) ℝ) :
      Matrix (Fin (a + e)) (Fin (a + e)) ℝ).submatrix id (Fin.castAdd e) =
      Kᵀ * C.submatrix id (Fin.castAdd e) := by
    rw [hg]
    ext p j
    simp [Matrix.mul_apply]
  have hgram : (Kᵀ * C.submatrix id (Fin.castAdd e))ᵀ * (Kᵀ * C.submatrix id (Fin.castAdd e)) =
      Tᵀ * T := by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc K, unitary_mul_transpose, Matrix.one_mul]
    ext j j'
    rw [Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_add]
    have hzero : ∑ p : Fin e, (C.submatrix id (Fin.castAdd e))ᵀ j (Fin.natAdd a p) *
        C.submatrix id (Fin.castAdd e) (Fin.natAdd a p) j' = 0 := by
      refine Finset.sum_eq_zero fun p _ => ?_
      have hz : C (Fin.natAdd a p) (Fin.castAdd e j) = 0 := hCu (show
        id (Fin.castAdd e j) < id (Fin.natAdd a p) from by
          rw [Fin.lt_def]; simp only [id, Fin.val_castAdd, Fin.val_natAdd]; omega)
      simp only [Matrix.transpose_apply, Matrix.submatrix_apply, id]
      rw [hz, zero_mul]
    rw [hzero, add_zero]
    rfl
  have hTu : T.BlockTriangular id := by
    intro i j hij
    exact hCu (show id (Fin.castAdd e j) < id (Fin.castAdd e i) from by
      rw [Fin.lt_def]; simp only [id, Fin.val_castAdd]; exact hij)
  have hprod : ∏ j, T j j = Real.exp (-∑ j : Fin a, alpha g (Fin.castAdd e j)) := by
    rw [← Finset.sum_neg_distrib, Real.exp_sum]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hT, Matrix.submatrix_apply, hC, bpart_inv_diag]
  rw [hsub, hgram, Matrix.det_mul, Matrix.det_transpose, Matrix.det_of_isUpperTriangular hTu,
    hprod, ← Real.exp_add]
  congr 1
  ring

/-! ### `det(1 + ᵗx x) ≥ 1 + ∑ x²` -/

theorem prod_one_add_ge {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    1 + ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 + f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have h1 := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have h2 := hf j (Finset.mem_insert_self j s)
    have h3 : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)
    nlinarith

/-- For a real rectangular matrix `x`, `det(1 + ᵗx x) ≥ 1 + ∑_(l,j) x_(lj)²`. -/
theorem one_add_sum_sq_le_det {d a : ℕ} (x : Matrix (Fin d) (Fin a) ℝ) :
    1 + ∑ l, ∑ j, x l j ^ 2 ≤ Matrix.det (1 + xᵀ * x) := by
  have hA : (xᵀ * x).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_conjTranspose_mul_self x
  have hB : (1 + xᵀ * x).IsHermitian := Matrix.isHermitian_one.add hA.1
  -- the eigenvalues of `1 + ᵗx x` are at least one
  have hμ : ∀ i, 1 ≤ hB.eigenvalues i := by
    intro i
    rw [hB.eigenvalues_eq i]
    have h := hB.eigenvectorBasis.orthonormal.1 i
    have hunit : star ⇑(hB.eigenvectorBasis i) ⬝ᵥ ⇑(hB.eigenvectorBasis i) = (1 : ℝ) := by
      have e : star ⇑(hB.eigenvectorBasis i) ⬝ᵥ ⇑(hB.eigenvectorBasis i) =
          inner ℝ (hB.eigenvectorBasis i) (hB.eigenvectorBasis i) := by
        rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
      rw [e, real_inner_self_eq_norm_sq, h, one_pow]
    have hpos := hA.dotProduct_mulVec_nonneg ⇑(hB.eigenvectorBasis i)
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, hunit]
    simp only [RCLike.re_to_real]
    linarith
  have hdet : Matrix.det (1 + xᵀ * x) = ∏ i, hB.eigenvalues i := by
    rw [hB.det_eq_prod_eigenvalues]
    simp
  have htr : Matrix.trace (1 + xᵀ * x) = ∑ i, hB.eigenvalues i := by
    rw [hB.trace_eq_sum_eigenvalues]
    simp
  have htr' : Matrix.trace (1 + xᵀ * x) = a + ∑ l, ∑ j, x l j ^ 2 := by
    rw [Matrix.trace_add, Matrix.trace_one, Fintype.card_fin, Matrix.trace]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp [Matrix.mul_apply, sq]
  have key := prod_one_add_ge Finset.univ (fun i => hB.eigenvalues i - 1)
    (fun i _ => sub_nonneg.mpr (hμ i))
  simp only [add_sub_cancel] at key
  rw [hdet]
  refine le_trans ?_ key
  rw [Finset.sum_sub_distrib, ← htr, htr']
  simp

/-! ### The determinant and reindexing -/

/-- `log |det g| = ∑_i α_i(g)`. -/
theorem log_abs_det_eq_sum_alpha (g : Langlands.GeneralLinear n ℝ) :
    Real.log |Matrix.det (g : Matrix (Fin n) (Fin n) ℝ)| = ∑ i, alpha g i := by
  have h := npart_mul_torus_mul_kpart g
  have hdet : Matrix.det (g : Matrix (Fin n) (Fin n) ℝ) = Real.exp (∑ i, alpha g i) *
      Matrix.det ((kpart g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
    conv_lhs => rw [← h]
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      Langlands.RankinSelberg.unipotent_det, one_mul, torus_val, Matrix.det_diagonal,
      Real.exp_sum]
  have hk : |Matrix.det ((kpart g : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ)| = 1 := by
    have hU : ((kpart g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) ∈
        Matrix.unitaryGroup (Fin n) ℝ := (kpart g).2
    have h1 := Matrix.det_of_mem_unitary hU
    have h2 := CStarRing.norm_of_mem_unitary h1
    rwa [Real.norm_eq_abs] at h2
  rw [hdet, abs_mul, hk, mul_one, abs_of_pos (Real.exp_pos _), Real.log_exp]

/-- Reindexing along an equality of sizes permutes nothing. -/
theorem alpha_reindex_finCongr {N N' : ℕ} (e : N = N') (g : Langlands.GeneralLinear N ℝ) :
    alpha (GeneralLinear.reindex (finCongr e) g) = fun i => alpha g (Fin.cast e.symm i) := by
  subst e
  have hg : GeneralLinear.reindex (finCongr (rfl : N = N)) g = g := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp [GeneralLinear.reindex]
  rw [hg]
  funext i
  simp

end Langlands.Global.RankinSelbergGlobal.RealIwasawa
