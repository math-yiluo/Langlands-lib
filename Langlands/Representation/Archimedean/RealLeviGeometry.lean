import Langlands.Representation.Archimedean.RealLeviParabolicIntegrationStatement
import Langlands.Representation.Archimedean.RealBlockLimit
import Langlands.Representation.Archimedean.RealBlockRotation
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Geometry of the opposite unipotent radical of a standard parabolic subgroup of `GL_N(ℝ)`

For the upper block triangular parabolic subgroup `Q` with blocks of sizes `sz` (module
`RealLeviChartIntegralStatement`), this module proves:

* scaling by the centre of the Levi factor: `n̄(X) d_s = d_s n̄(X_s)` for
  `d_s = diag(s^{cls p})`, with `(X_s)_{pq} = s^{cls q - cls p} X_{pq}`;
* conjugation by block orthogonal matrices `k` (orthogonal, no entries between different blocks):
  `k n̄(X) = n̄(Ad(k) X) k`, where `Ad(k)` is a linear map preserving Lebesgue measure and commuting
  with the scaling; block rotations inside a block and block diagonal orthogonal matrices are
  block orthogonal;
* Gram determinants of `n̄(X)`: `1 ≤ G_l(n̄(X))` and `G_l(n̄(X_s)) ≤ G_l(n̄(X))` for `s ≥ 1`.

`RealLeviGeometryStatement` collects these facts; `realLeviGeometry` proves it.
-/

noncomputable section

open MeasureTheory Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace RealLeviChart

open GramFormula

/-! ## Determinant inequalities -/

section Det

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
theorem posSemidef_transpose_mul_self' {m : Type*} [Fintype m] (C : Matrix m ι ℝ) :
    (Cᵀ * C).PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self C
  rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem posDef_one_add_transpose_mul_self {m : Type*} [Fintype m] (C : Matrix m ι ℝ) :
    (1 + Cᵀ * C).PosDef :=
  Matrix.PosDef.one.add_posSemidef (posSemidef_transpose_mul_self' C)

/-- `det A ≤ det (A + Cᵀ C)` for positive definite `A`. -/
theorem det_le_det_add_transpose_mul_self [DecidableEq κ] {A : Matrix ι ι ℝ} (hA : A.PosDef) (C : Matrix κ ι ℝ) :
    A.det ≤ (A + Cᵀ * C).det := by
  have hu : IsUnit A.det := (hA.det_pos).ne'.isUnit
  rw [Matrix.det_add_mul Cᵀ C hu]
  have hP : (C * A⁻¹ * Cᵀ).PosSemidef := by
    have h := (hA.posSemidef.inv).conjTranspose_mul_mul_same Cᵀ
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] at h
  have h1 : 1 ≤ (1 + C * A⁻¹ * Cᵀ).det := by
    simpa using RealBlockLimit.one_le_det hP zero_le_one
  have h0 : 0 < A.det := hA.det_pos
  nlinarith

/-- Diagonal contractions decrease `det (1 + Y Yᵀ)`. -/
theorem det_one_add_contraction_le (Y : Matrix ι ι ℝ) {a b : ι → ℝ} (ha : ∀ i, |a i| ≤ 1)
    (hb : ∀ i, |b i| ≤ 1) :
    (1 + (diagonal a * Y * diagonal b) * (diagonal a * Y * diagonal b)ᵀ).det ≤
      (1 + Y * Yᵀ).det := by
  set Y' := diagonal a * Y * diagonal b
  have ha' : ∀ i, 0 ≤ 1 - a i ^ 2 := fun i => by
    have := ha i
    nlinarith [abs_nonneg (a i), sq_abs (a i)]
  have hb' : ∀ i, 0 ≤ 1 - b i ^ 2 := fun i => by
    have := hb i
    nlinarith [abs_nonneg (b i), sq_abs (b i)]
  -- Step 1: `det (1 + Y' Y'ᵀ) = det (1 + Y'ᵀ Y') ≤ det (1 + (Y B)ᵀ (Y B))`.
  have e1 : (1 + Y' * Y'ᵀ).det = (1 + Y'ᵀ * Y').det := Matrix.det_one_add_mul_comm _ _
  set C1 := diagonal (fun i => Real.sqrt (1 - a i ^ 2)) * Y * diagonal b
  have e2 : 1 + Y'ᵀ * Y' + C1ᵀ * C1 = 1 + (Y * diagonal b)ᵀ * (Y * diagonal b) := by
    have hd : diagonal a * diagonal a +
        diagonal (fun i => Real.sqrt (1 - a i ^ 2)) * diagonal (fun i => Real.sqrt (1 - a i ^ 2)) =
          (1 : Matrix ι ι ℝ) := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [Real.mul_self_sqrt (ha' i)]
      ring
    have hY' : Y'ᵀ * Y' = (Y * diagonal b)ᵀ * (diagonal a * diagonal a) * (Y * diagonal b) := by
      simp only [Y', Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    have hC : C1ᵀ * C1 = (Y * diagonal b)ᵀ * (diagonal (fun i => Real.sqrt (1 - a i ^ 2)) *
        diagonal (fun i => Real.sqrt (1 - a i ^ 2))) * (Y * diagonal b) := by
      simp only [C1, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    rw [hY', hC, add_assoc, ← Matrix.add_mul, ← Matrix.mul_add, hd, Matrix.mul_one]
  have s1 : (1 + Y'ᵀ * Y').det ≤ (1 + (Y * diagonal b)ᵀ * (Y * diagonal b)).det := by
    rw [← e2]
    exact det_le_det_add_transpose_mul_self (posDef_one_add_transpose_mul_self Y') C1
  -- Step 2: `det (1 + (Y B)ᵀ (Y B)) = det (1 + (Y B)(Y B)ᵀ) ≤ det (1 + Y Yᵀ)`.
  have e3 : (1 + (Y * diagonal b)ᵀ * (Y * diagonal b)).det =
      (1 + (Y * diagonal b) * (Y * diagonal b)ᵀ).det := Matrix.det_one_add_mul_comm _ _
  set C2 := diagonal (fun i => Real.sqrt (1 - b i ^ 2)) * Yᵀ
  have e4 : 1 + (Y * diagonal b) * (Y * diagonal b)ᵀ + C2ᵀ * C2 = 1 + Y * Yᵀ := by
    have hd : diagonal b * diagonal b +
        diagonal (fun i => Real.sqrt (1 - b i ^ 2)) * diagonal (fun i => Real.sqrt (1 - b i ^ 2)) =
          (1 : Matrix ι ι ℝ) := by
      rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      rw [Real.mul_self_sqrt (hb' i)]
      ring
    have h1 : (Y * diagonal b) * (Y * diagonal b)ᵀ = Y * (diagonal b * diagonal b) * Yᵀ := by
      simp only [Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc]
    have h2 : C2ᵀ * C2 = Y * (diagonal (fun i => Real.sqrt (1 - b i ^ 2)) *
        diagonal (fun i => Real.sqrt (1 - b i ^ 2))) * Yᵀ := by
      simp only [C2, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.transpose_transpose,
        Matrix.mul_assoc]
    rw [h1, h2, add_assoc, ← Matrix.add_mul, ← Matrix.mul_add, hd, Matrix.mul_one]
  have s2 : (1 + (Y * diagonal b) * (Y * diagonal b)ᵀ).det ≤ (1 + Y * Yᵀ).det := by
    rw [← e4]
    have hpd : (1 + (Y * diagonal b) * (Y * diagonal b)ᵀ).PosDef := by
      have := posDef_one_add_transpose_mul_self (Y * diagonal b)ᵀ
      rwa [Matrix.transpose_transpose] at this
    exact det_le_det_add_transpose_mul_self hpd C2
  rw [e1]
  exact s1.trans (e3 ▸ s2)

end Det

/-! ## Gram determinants of block factorizations -/

section Gram

variable {n : ℕ}

/-- The block of `Z` on the rows `≥ l` and the columns `< l`, padded by zeros. -/
def lowerLeft (l : ℕ) (Z : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if l ≤ (p : ℕ) ∧ (q : ℕ) < l then Z p q else 0

theorem padded_apply_of_le_of_blockUpper (l : ℕ) {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → W p q = 0) {p : Fin n}
    (hp : l ≤ (p : ℕ)) (q : Fin n) : padded l W p q = W p q := by
  simp only [padded, Matrix.of_apply]
  by_cases hq : l ≤ (q : ℕ)
  · rw [ite_eq_left ⟨hp, hq⟩]
  · rw [ite_eq_right (fun h => hq h.2), hW p q hp (by omega), Matrix.one_apply_ne]
    intro hpq
    subst hpq
    omega

theorem mul_apply_of_row_single {A B : Matrix (Fin n) (Fin n) ℝ} {p : Fin n}
    (h : A p = Pi.single p 1) (q : Fin n) : (A * B) p q = B p q := by
  rw [Matrix.mul_apply]
  simp [h, Pi.single_apply]

theorem mul_transpose_apply_of_row_single {A B : Matrix (Fin n) (Fin n) ℝ} {q : Fin n}
    (h : B q = Pi.single q 1) (p : Fin n) : (A * Bᵀ) p q = A p q := by
  rw [Matrix.mul_apply]
  simp [Matrix.transpose_apply, h, Pi.single_apply]

theorem row_paddedGram_of_lt (l : ℕ) (Z : Matrix (Fin n) (Fin n) ℝ) {p : Fin n}
    (hp : (p : ℕ) < l) : paddedGram l Z p = Pi.single p 1 := by
  funext q
  simp only [paddedGram, Matrix.of_apply]
  rw [ite_eq_right (fun h => absurd h.1 (by omega)), Matrix.one_apply, Pi.single_apply]
  by_cases h : p = q
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- For `W` without entries on the rows `≥ l` and the columns `< l`, the padded Gram matrix of
`W Z` is the conjugate of that of `Z` by the padded `W`. -/
theorem paddedGram_mul_of_blockUpper (l : ℕ) {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → W p q = 0) (Z : Matrix (Fin n) (Fin n) ℝ) :
    paddedGram l (W * Z) = padded l W * paddedGram l Z * (padded l W)ᵀ := by
  ext p q
  by_cases hp : l ≤ (p : ℕ)
  · by_cases hq : l ≤ (q : ℕ)
    · have lhs : paddedGram l (W * Z) p q = (W * (Z * Zᵀ) * Wᵀ) p q := by
        simp only [paddedGram, Matrix.of_apply]
        rw [ite_eq_left ⟨hp, hq⟩, Matrix.transpose_mul, Matrix.mul_assoc, Matrix.mul_assoc,
          Matrix.mul_assoc]
      rw [lhs]
      simp only [Matrix.mul_apply, Matrix.transpose_apply]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [padded_apply_of_le_of_blockUpper l hW hp, padded_apply_of_le_of_blockUpper l hW hq]
      by_cases hr : (r : ℕ) < l
      · rw [hW p r hp hr]
        ring
      · by_cases ht : (t : ℕ) < l
        · rw [hW q t hq ht]
          ring
        · simp only [paddedGram, Matrix.of_apply]
          rw [ite_eq_left ⟨by omega, by omega⟩]
          simp only [Matrix.mul_apply, Matrix.transpose_apply]
    · have hq' : (q : ℕ) < l := by omega
      rw [mul_transpose_apply_of_row_single (row_padded_of_lt W hq'),
        Matrix.mul_apply]
      simp only [paddedGram, Matrix.of_apply]
      rw [ite_eq_right (fun h => hq h.2), Matrix.one_apply_ne (fun h => by subst h; omega)]
      symm
      refine Finset.sum_eq_zero fun r _ => ?_
      rw [ite_eq_right (fun h => by omega)]
      by_cases hr : r = q
      · subst hr
        rw [padded_apply_of_le_of_blockUpper l hW hp, hW p r hp hq']
        ring
      · rw [Matrix.one_apply_ne hr]
        ring
  · have hp' : (p : ℕ) < l := by omega
    have hrow : (padded l W * paddedGram l Z) p = Pi.single p 1 := by
      funext t
      rw [mul_apply_of_row_single (row_padded_of_lt W hp')]
      exact congrFun (row_paddedGram_of_lt l Z hp') t
    rw [Matrix.mul_apply]
    simp only [hrow, Matrix.transpose_apply, Pi.single_apply]
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    simp only [paddedGram, Matrix.of_apply]
    rw [ite_eq_right (fun h => absurd h.1 hp)]
    by_cases hq : l ≤ (q : ℕ)
    · rw [padded_apply_of_le_of_blockUpper l hW hq, hW q p hq hp',
        Matrix.one_apply_ne (fun h => by subst h; omega)]
    · rw [padded_apply_of_lt W (by omega), Matrix.one_apply, Matrix.one_apply]
      by_cases h : p = q
      · subst h
        simp
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem det_padded_of_lower (l : ℕ) {W : Matrix (Fin n) (Fin n) ℝ} (hW : W.IsLowerTriangular)
    (hW1 : ∀ p, W p p = 1) : (padded l W).det = 1 := by
  have hlt : (padded l W).IsLowerTriangular := by
    intro p q hpq
    simp only [padded, Matrix.of_apply]
    split_ifs
    · exact hW hpq
    · exact Matrix.one_apply_ne (ne_of_lt hpq)
  rw [Matrix.det_of_isLowerTriangular _ hlt]
  refine Finset.prod_eq_one fun p _ => ?_
  simp only [padded, Matrix.of_apply]
  split_ifs
  · exact hW1 p
  · exact Matrix.one_apply_eq p

theorem gram_mul_of_blockUpper (l : ℕ) {W : Matrix (Fin n) (Fin n) ℝ}
    (hW : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → W p q = 0) (hWl : W.IsLowerTriangular)
    (hW1 : ∀ p, W p p = 1) (Z : Matrix (Fin n) (Fin n) ℝ) : gram l (W * Z) = gram l Z := by
  rw [gram, gram, paddedGram_mul_of_blockUpper l hW, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_transpose, det_padded_of_lower l hWl hW1]
  ring

/-- If `Z` is the identity on the rows and columns `≥ l`, then `G_l(Z) = det (1 + Y Yᵀ)` for the
lower left block `Y` of `Z`. -/
theorem paddedGram_of_block_one (l : ℕ) {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : ∀ p q : Fin n, l ≤ (p : ℕ) → l ≤ (q : ℕ) → Z p q = (1 : Matrix (Fin n) (Fin n) ℝ) p q) :
    paddedGram l Z = 1 + lowerLeft l Z * (lowerLeft l Z)ᵀ := by
  ext p q
  simp only [paddedGram, Matrix.of_apply, Matrix.add_apply, Matrix.mul_apply,
    Matrix.transpose_apply, lowerLeft]
  by_cases hp : l ≤ (p : ℕ)
  · by_cases hq : l ≤ (q : ℕ)
    · rw [ite_eq_left ⟨hp, hq⟩]
      have h1 : ∀ r : Fin n, Z p r * Z q r =
          (1 : Matrix (Fin n) (Fin n) ℝ) p r * (1 : Matrix (Fin n) (Fin n) ℝ) q r +
            (if l ≤ (p : ℕ) ∧ (r : ℕ) < l then Z p r else 0) *
              (if l ≤ (q : ℕ) ∧ (r : ℕ) < l then Z q r else 0) := by
        intro r
        by_cases hr : (r : ℕ) < l
        · rw [ite_eq_left ⟨hp, hr⟩, ite_eq_left ⟨hq, hr⟩,
            Matrix.one_apply_ne (fun h => by subst h; omega), zero_mul, zero_add]
        · rw [ite_eq_right (fun h => hr h.2), ite_eq_right (fun h => hr h.2), mul_zero, add_zero,
            hZ p r hp (by omega), hZ q r hq (by omega)]
      rw [Finset.sum_congr rfl fun r _ => h1 r, Finset.sum_add_distrib]
      congr 1
      have := congrFun (congrFun (Matrix.mul_one (1 : Matrix (Fin n) (Fin n) ℝ)) p) q
      rw [← this, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Matrix.one_apply, Matrix.one_apply, Matrix.one_apply]
      by_cases h : q = r
      · subst h
        simp
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    · rw [ite_eq_right (fun h => hq h.2)]
      have : ∑ r : Fin n, (if l ≤ (p : ℕ) ∧ (r : ℕ) < l then Z p r else 0) *
          (if l ≤ (q : ℕ) ∧ (r : ℕ) < l then Z q r else 0) = 0 :=
        Finset.sum_eq_zero fun r _ => by
          rw [ite_eq_right (show ¬(l ≤ (q : ℕ) ∧ (r : ℕ) < l) from fun h => hq h.1), mul_zero]
      rw [this, add_zero]
  · rw [ite_eq_right (fun h => hp h.1)]
    have : ∑ r : Fin n, (if l ≤ (p : ℕ) ∧ (r : ℕ) < l then Z p r else 0) *
        (if l ≤ (q : ℕ) ∧ (r : ℕ) < l then Z q r else 0) = 0 :=
      Finset.sum_eq_zero fun r _ => by rw [ite_eq_right (fun h => hp h.1), zero_mul]
    rw [this, add_zero]

theorem gram_of_block_one (l : ℕ) {Z : Matrix (Fin n) (Fin n) ℝ}
    (hZ : ∀ p q : Fin n, l ≤ (p : ℕ) → l ≤ (q : ℕ) → Z p q = (1 : Matrix (Fin n) (Fin n) ℝ) p q) :
    gram l Z = (1 + lowerLeft l Z * (lowerLeft l Z)ᵀ).det := by
  rw [gram, paddedGram_of_block_one l hZ]

/-- The block diagonal part of `L` for the splitting of the indices at `l`. -/
def splitDiag (l : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun p q => if (l ≤ (p : ℕ) ↔ l ≤ (q : ℕ)) then L p q else 0

/-- The projection onto the coordinates `≥ l`. -/
def splitProj (l : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun p => if l ≤ (p : ℕ) then 1 else 0

section Factor

variable {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular) (hL1 : ∀ p, L p p = 1)
include hL hL1

omit hL1 in
theorem splitDiag_isLowerTriangular (l : ℕ) : (splitDiag l L).IsLowerTriangular := by
  intro p q hpq
  simp only [splitDiag, Matrix.of_apply]
  split_ifs
  · exact hL hpq
  · rfl

omit hL in
theorem splitDiag_apply_self (l : ℕ) (p : Fin n) : splitDiag l L p p = 1 := by
  simp only [splitDiag, Matrix.of_apply, iff_self, ite_true]
  exact hL1 p

theorem det_splitDiag (l : ℕ) : (splitDiag l L).det = 1 := by
  rw [Matrix.det_of_isLowerTriangular _ (splitDiag_isLowerTriangular hL l)]
  exact Finset.prod_eq_one fun p _ => splitDiag_apply_self hL1 l p

/-- The factor `Z = W⁻¹ L` of `L = W Z`, `W` the block diagonal part. -/
def splitFactor (l : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (splitDiag l L)⁻¹ * L

theorem splitDiag_mul_splitFactor (l : ℕ) : splitDiag l L * splitFactor l L = L := by
  rw [splitFactor, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _
    (by rw [det_splitDiag hL hL1]; exact isUnit_one), Matrix.one_mul]

theorem splitFactor_block_one (l : ℕ) (p q : Fin n) (hp : l ≤ (p : ℕ)) (hq : l ≤ (q : ℕ)) :
    splitFactor l L p q = (1 : Matrix (Fin n) (Fin n) ℝ) p q := by
  set W := splitDiag l L
  set P := (splitProj l : Matrix (Fin n) (Fin n) ℝ)
  have hu : IsUnit W.det := by rw [det_splitDiag hL hL1]; exact isUnit_one
  have hWP : W * P = P * W := by
    ext a b
    simp only [P, splitProj, Matrix.mul_diagonal, Matrix.diagonal_mul, W, splitDiag,
      Matrix.of_apply]
    by_cases ha : l ≤ (a : ℕ) <;> by_cases hb : l ≤ (b : ℕ) <;> simp [ha, hb]
  have hPW : P * W⁻¹ = W⁻¹ * P := by
    calc P * W⁻¹ = W⁻¹ * (W * P) * W⁻¹ := by
          rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
      _ = W⁻¹ * (P * W) * W⁻¹ := by rw [hWP]
      _ = W⁻¹ * P := by
          rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]
  have hPLP : P * L * P = W * P := by
    ext a b
    simp only [P, splitProj, Matrix.mul_diagonal, Matrix.diagonal_mul, W, splitDiag,
      Matrix.of_apply]
    by_cases ha : l ≤ (a : ℕ) <;> by_cases hb : l ≤ (b : ℕ) <;> simp [ha, hb]
  have hZ : P * splitFactor l L * P = P := by
    calc P * splitFactor l L * P = P * W⁻¹ * L * P := by
          simp only [splitFactor, W, Matrix.mul_assoc]
      _ = W⁻¹ * (P * L * P) := by
          rw [hPW]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hPLP, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
  have := congrFun (congrFun hZ p) q
  simp only [P, splitProj, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.diagonal_apply,
    hp, hq, ite_true, one_mul, mul_one] at this
  rw [this, Matrix.one_apply]

end Factor

/-- `G_l(L) = det (1 + Y Yᵀ)` for a lower unitriangular `L`. -/
theorem gram_eq_of_lower {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hL1 : ∀ p, L p p = 1) (l : ℕ) :
    gram l L = (1 + lowerLeft l (splitFactor l L) * (lowerLeft l (splitFactor l L))ᵀ).det := by
  have hW : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → splitDiag l L p q = 0 := by
    intro p q hp hq
    simp only [splitDiag, Matrix.of_apply]
    rw [ite_eq_right (fun h => by have := h.mp hp; omega)]
  conv_lhs => rw [← splitDiag_mul_splitFactor hL hL1 l]
  rw [gram_mul_of_blockUpper l hW (splitDiag_isLowerTriangular hL l)
    (splitDiag_apply_self hL1 l), gram_of_block_one l (splitFactor_block_one hL hL1 l)]

theorem one_le_gram_of_lower {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hL1 : ∀ p, L p p = 1) (l : ℕ) : 1 ≤ gram l L := by
  rw [gram_eq_of_lower hL hL1 l]
  have h := det_le_det_add_transpose_mul_self (Matrix.PosDef.one (n := Fin n) (R := ℝ))
    (lowerLeft l (splitFactor l L))ᵀ
  rwa [Matrix.det_one, Matrix.transpose_transpose] at h

/-- **Gram monotonicity.** Conjugating a lower unitriangular `L` by a positive diagonal matrix `d`
that is `≤ μ` on the coordinates `< l` and `≥ μ` on the coordinates `≥ l` decreases `G_l`. -/
theorem gram_conj_le {L : Matrix (Fin n) (Fin n) ℝ} (hL : L.IsLowerTriangular)
    (hL1 : ∀ p, L p p = 1) (l : ℕ) {d : Fin n → ℝ} (hd : ∀ p, 0 < d p) {μ : ℝ} (hμ : 0 < μ)
    (h1 : ∀ q : Fin n, (q : ℕ) < l → d q ≤ μ) (h2 : ∀ p : Fin n, l ≤ (p : ℕ) → μ ≤ d p) :
    gram l (diagonal (fun p => (d p)⁻¹) * L * diagonal d) ≤ gram l L := by
  set Di := (diagonal fun p => (d p)⁻¹ : Matrix (Fin n) (Fin n) ℝ)
  set Dm := (diagonal d : Matrix (Fin n) (Fin n) ℝ)
  have hDmDi : Dm * Di = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext p
    exact mul_inv_cancel₀ (hd p).ne'
  have hfac : Di * L * Dm = (Di * splitDiag l L * Dm) * (Di * splitFactor l L * Dm) := by
    conv_lhs => rw [← splitDiag_mul_splitFactor hL hL1 l]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Dm Di, hDmDi, Matrix.one_mul]
  have hconj : ∀ (A : Matrix (Fin n) (Fin n) ℝ) (p q : Fin n),
      (Di * A * Dm) p q = (d p)⁻¹ * A p q * d q := by
    intro A p q
    simp only [Di, Dm, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hW : ∀ p q : Fin n, l ≤ (p : ℕ) → (q : ℕ) < l → (Di * splitDiag l L * Dm) p q = 0 := by
    intro p q hp hq
    rw [hconj]
    simp only [splitDiag, Matrix.of_apply]
    rw [ite_eq_right (fun h => by have := h.mp hp; omega)]
    ring
  have hWl : (Di * splitDiag l L * Dm).IsLowerTriangular := by
    intro p q hpq
    rw [hconj, splitDiag_isLowerTriangular hL l hpq]
    ring
  have hW1 : ∀ p, (Di * splitDiag l L * Dm) p p = 1 := by
    intro p
    rw [hconj, splitDiag_apply_self hL1 l, mul_one, inv_mul_cancel₀ (hd p).ne']
  have hZ : ∀ p q : Fin n, l ≤ (p : ℕ) → l ≤ (q : ℕ) →
      (Di * splitFactor l L * Dm) p q = (1 : Matrix (Fin n) (Fin n) ℝ) p q := by
    intro p q hp hq
    rw [hconj, splitFactor_block_one hL hL1 l p q hp hq, Matrix.one_apply]
    by_cases h : p = q
    · subst h
      rw [ite_eq_left rfl, mul_one, inv_mul_cancel₀ (hd p).ne']
    · rw [ite_eq_right h]
      ring
  rw [hfac, gram_mul_of_blockUpper l hW hWl hW1, gram_of_block_one l hZ, gram_eq_of_lower hL hL1 l]
  have hY : lowerLeft l (Di * splitFactor l L * Dm) =
      diagonal (fun p : Fin n => if l ≤ (p : ℕ) then μ / d p else 0) * lowerLeft l (splitFactor l L) *
        diagonal (fun q : Fin n => if (q : ℕ) < l then d q / μ else 0) := by
    ext p q
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [lowerLeft, Matrix.of_apply]
    by_cases hp : l ≤ (p : ℕ)
    · by_cases hq : (q : ℕ) < l
      · simp only [hp, hq, and_self, ↓reduceIte, hconj]
        field_simp [(hd p).ne', (hd q).ne', hμ.ne']
      · simp [hq]
    · simp [hp]
  rw [hY]
  refine det_one_add_contraction_le _ (fun p => ?_) (fun q => ?_)
  · split_ifs with hp
    · rw [abs_of_pos (div_pos hμ (hd p)), div_le_one (hd p)]
      exact h2 p hp
    · simp
  · split_ifs with hq
    · rw [abs_of_pos (div_pos (hd q) hμ), div_le_one hμ]
      exact h1 q hq
    · simp

end Gram

/-! ## Scaling by the centre of the Levi factor -/

section Scale

variable {c : ℕ} (sz : Fin c → ℕ)

theorem cls_mono {p q : Fin (∑ i, sz i)} (hpq : p ≤ q) : cls sz p ≤ cls sz q :=
  not_lt.mp fun h => absurd (lt_of_cls_lt sz h) (not_lt.mpr hpq)

theorem lower_apply_of_not_lt (X : Coord sz → ℝ) {p q : Fin (∑ i, sz i)}
    (h : ¬ cls sz q < cls sz p) : lower sz X p q = (1 : Matrix _ _ ℝ) p q := by
  simp only [lower, Matrix.of_apply, h, ↓reduceDIte, Matrix.one_apply]

theorem lower_injective : Function.Injective (lower sz) := by
  intro X Y h
  funext pq
  have := congrFun (congrFun h pq.1.1) pq.1.2
  simpa only [lower, Matrix.of_apply, pq.2, ↓reduceDIte] using this

/-- The weights `s^{cls p}` of `d_s = diag(s^{cls p})`. -/
def scaleVec (s : ℝ) (p : Fin (∑ i, sz i)) : ℝ := s ^ ((cls sz p : ℕ))

theorem scaleVec_pos {s : ℝ} (hs : 0 < s) (p : Fin (∑ i, sz i)) : 0 < scaleVec sz s p :=
  pow_pos hs _

/-- `X_s`: `(X_s)_{pq} = s^{cls q} s^{-cls p} X_{pq}`, so that `n̄(X) d_s = d_s n̄(X_s)`. -/
def scaleCoord (s : ℝ) (X : Coord sz → ℝ) : Coord sz → ℝ :=
  fun pq => scaleVec sz s pq.1.2 / scaleVec sz s pq.1.1 * X pq

theorem lower_mul_diagonal {s : ℝ} (hs : 0 < s) (X : Coord sz → ℝ) :
    lower sz X * diagonal (scaleVec sz s) =
      diagonal (scaleVec sz s) * lower sz (scaleCoord sz s X) := by
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hp := (scaleVec_pos sz hs p).ne'
  by_cases h : cls sz q < cls sz p
  · simp only [lower, Matrix.of_apply, h, ↓reduceDIte, scaleCoord]
    field_simp
  · rw [lower_apply_of_not_lt sz X h, lower_apply_of_not_lt sz _ h, Matrix.one_apply]
    by_cases hpq : p = q
    · subst hpq
      simp
    · simp [hpq]

theorem lower_scaleCoord {s : ℝ} (hs : 0 < s) (X : Coord sz → ℝ) :
    lower sz (scaleCoord sz s X) =
      diagonal (fun p => (scaleVec sz s p)⁻¹) * lower sz X * diagonal (scaleVec sz s) := by
  rw [Matrix.mul_assoc, lower_mul_diagonal sz hs, ← Matrix.mul_assoc, Matrix.diagonal_mul_diagonal]
  have : (fun p => (scaleVec sz s p)⁻¹ * scaleVec sz s p) = fun _ => (1 : ℝ) :=
    funext fun p => inv_mul_cancel₀ (scaleVec_pos sz hs p).ne'
  rw [this, Matrix.diagonal_one, Matrix.one_mul]

/-- `d_s = diag(s^{cls p}) ∈ GL_N(ℝ)` for `s > 0`. -/
def scaleGL {s : ℝ} (hs : 0 < s) : Langlands.GeneralLinear (∑ i, sz i) ℝ :=
  Langlands.GeneralLinear.Iwasawa.diagonalUnits fun p => Units.mk0 (scaleVec sz s p)
    (scaleVec_pos sz hs p).ne'

theorem scaleGL_val {s : ℝ} (hs : 0 < s) :
    ((scaleGL sz hs : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
      Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) = diagonal (scaleVec sz s) := rfl

/-- `n̄(X) d_s = d_s n̄(X_s)`. -/
theorem lowerGL_mul_scaleGL {s : ℝ} (hs : 0 < s) (X : Coord sz → ℝ) :
    lowerGL sz X * scaleGL sz hs = scaleGL sz hs * lowerGL sz (scaleCoord sz s X) := by
  ext : 1
  simp only [Units.val_mul, lowerGL_val, scaleGL_val]
  exact lower_mul_diagonal sz hs X

/-- **Gram monotonicity under scaling.** For `s ≥ 1`, `G_l(n̄(X_s)) ≤ G_l(n̄(X))`. -/
theorem gram_lower_scaleCoord_le {s : ℝ} (hs : 1 ≤ s) (X : Coord sz → ℝ) (l : ℕ) :
    gram l (lower sz (scaleCoord sz s X)) ≤ gram l (lower sz X) := by
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  rw [lower_scaleCoord sz hs0]
  by_cases hl : l < ∑ i, sz i
  · set m : Fin (∑ i, sz i) := ⟨l, hl⟩
    refine gram_conj_le (lower_isLowerTriangular sz X) (lower_apply_self sz X) l
      (scaleVec_pos sz hs0) (scaleVec_pos sz hs0 m) (fun q hq => ?_) (fun p hp => ?_)
    · exact pow_le_pow_right₀ hs (cls_mono sz (Fin.le_def.mpr hq.le))
    · exact pow_le_pow_right₀ hs (cls_mono sz (Fin.le_def.mpr hp))
  · have h1 : ∀ M : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ, gram l M = 1 := by
      intro M
      have : paddedGram l M = 1 := by
        ext p q
        simp only [paddedGram, Matrix.of_apply]
        rw [ite_eq_right (fun h => absurd h.1 (by omega))]
      rw [gram, this, Matrix.det_one]
    rw [h1, h1]

theorem one_le_gram_lower (X : Coord sz → ℝ) (l : ℕ) : 1 ≤ gram l (lower sz X) :=
  one_le_gram_of_lower (lower_isLowerTriangular sz X) (lower_apply_self sz X) l

end Scale

/-! ## Block orthogonal matrices -/

section BlockOrth

variable {c : ℕ} (sz : Fin c → ℕ)

/-- `k` has no entries between different blocks. -/
def BlockZero (k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) : Prop :=
  ∀ p q, cls sz p ≠ cls sz q → k p q = 0

/-- The block orthogonal elements of `GL_N(ℝ)`: orthogonal, without entries between different
blocks. -/
def blockOrth : Subgroup (Langlands.GeneralLinear (∑ i, sz i) ℝ) where
  carrier := {g | (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) *
      (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)ᵀ = 1 ∧
    BlockZero sz (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)}
  mul_mem' {g h} hg hh := by
    refine ⟨?_, ?_⟩
    · simp only [Units.val_mul, Matrix.transpose_mul]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((h : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
        Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ), hh.1, Matrix.one_mul, hg.1]
    · intro p q hpq
      simp only [Units.val_mul, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun r _ => ?_
      by_cases hr : cls sz p = cls sz r
      · rw [hh.2 r q (fun h' => hpq (hr.trans h')), mul_zero]
      · rw [hg.2 p r hr, zero_mul]
  one_mem' := by
    refine ⟨by simp, fun p q hpq => ?_⟩
    simp only [Units.val_one]
    exact Matrix.one_apply_ne fun h => hpq (h ▸ rfl)
  inv_mem' {g} hg := by
    have hT : (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)ᵀ *
        (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) = 1 := mul_eq_one_comm.mp hg.1
    have hinv : ((g⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
        Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) =
          (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)ᵀ :=
      Units.inv_eq_of_mul_eq_one_right hg.1
    refine ⟨?_, fun p q hpq => ?_⟩
    · change ((g⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
        Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) *
          ((g⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
            Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)ᵀ = 1
      rw [hinv, Matrix.transpose_transpose, hT]
    · change ((g⁻¹ : Langlands.GeneralLinear (∑ i, sz i) ℝ) :
        Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) p q = 0
      rw [hinv, Matrix.transpose_apply]
      exact hg.2 q p (Ne.symm hpq)

variable {sz}

theorem transpose_mul_self_of_mem {g : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hg : g ∈ blockOrth sz) :
    (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)ᵀ *
      (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) = 1 :=
  mul_eq_one_comm.mp hg.1

theorem lower_conj_apply_of_not_lt {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hk : k * kᵀ = 1) (hz : BlockZero sz k) (X : Coord sz → ℝ) {p q : Fin (∑ i, sz i)}
    (hpq : ¬ cls sz q < cls sz p) :
    (k * lower sz X * kᵀ) p q = (1 : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) p q := by
  have : (k * lower sz X * kᵀ) p q =
      (k * (1 : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) * kᵀ :
        Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) p q := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun r _ => ?_
    by_cases hr : cls sz p = cls sz r
    · by_cases ht : cls sz q = cls sz t
      · have hrt : ¬ cls sz t < cls sz r := by rw [← hr, ← ht]; exact hpq
        rw [lower_apply_of_not_lt sz X hrt]
      · rw [hz q t ht]
        ring
    · rw [hz p r hr]
      ring
  rw [this, Matrix.mul_one, hk]

/-- `Ad(k) X`: the coordinates of `k n̄(X) kᵀ`. -/
def adCoord (k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) (X : Coord sz → ℝ) :
    Coord sz → ℝ :=
  fun pq => (k * lower sz X * kᵀ) pq.1.1 pq.1.2

theorem lower_adCoord {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ} (hk : k * kᵀ = 1)
    (hz : BlockZero sz k) (X : Coord sz → ℝ) :
    lower sz (adCoord k X) = k * lower sz X * kᵀ := by
  ext p q
  by_cases h : cls sz q < cls sz p
  · simp only [lower, Matrix.of_apply, h, ↓reduceDIte, adCoord]
  · rw [lower_conj_apply_of_not_lt hk hz X h, lower_apply_of_not_lt sz _ h]

/-- `k n̄(X) = n̄(Ad(k) X) k` for block orthogonal `k`. -/
theorem mul_lowerGL {g : Langlands.GeneralLinear (∑ i, sz i) ℝ} (hg : g ∈ blockOrth sz)
    (X : Coord sz → ℝ) :
    g * lowerGL sz X = lowerGL sz (adCoord (g : Matrix _ _ ℝ) X) * g := by
  ext : 1
  simp only [Units.val_mul, lowerGL_val]
  rw [lower_adCoord hg.1 hg.2, Matrix.mul_assoc, transpose_mul_self_of_mem hg, Matrix.mul_one]

theorem commute_diagonal_of_blockZero {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hz : BlockZero sz k) {v : Fin (∑ i, sz i) → ℝ}
    (hv : ∀ p q, cls sz p = cls sz q → v p = v q) : k * diagonal v = diagonal v * k := by
  ext p q
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases h : cls sz p = cls sz q
  · rw [hv p q h, mul_comm]
  · rw [hz p q h, mul_zero, zero_mul]

theorem mul_scaleGL {g : Langlands.GeneralLinear (∑ i, sz i) ℝ} (hg : g ∈ blockOrth sz)
    {s : ℝ} (hs : 0 < s) : g * scaleGL sz hs = scaleGL sz hs * g := by
  ext : 1
  simp only [Units.val_mul, scaleGL_val]
  exact commute_diagonal_of_blockZero hg.2 fun p q h => by simp only [scaleVec, h]

theorem adCoord_scaleCoord {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ} (hk : k * kᵀ = 1)
    (hz : BlockZero sz k) {s : ℝ} (hs : 0 < s) (X : Coord sz → ℝ) :
    adCoord k (scaleCoord sz s X) = scaleCoord sz s (adCoord k X) := by
  apply lower_injective sz
  have hv : ∀ p q, cls sz p = cls sz q → scaleVec sz s p = scaleVec sz s q :=
    fun p q h => by simp only [scaleVec, h]
  have hvi : ∀ p q, cls sz p = cls sz q → (scaleVec sz s p)⁻¹ = (scaleVec sz s q)⁻¹ :=
    fun p q h => by rw [hv p q h]
  have hkT : BlockZero sz kᵀ := fun p q h => hz q p (Ne.symm h)
  rw [lower_adCoord hk hz, lower_scaleCoord sz hs, lower_scaleCoord sz hs, lower_adCoord hk hz]
  have h1 := commute_diagonal_of_blockZero hz hvi
  have h2 := commute_diagonal_of_blockZero hkT hv
  calc k * ((diagonal fun p => (scaleVec sz s p)⁻¹) * lower sz X * diagonal (scaleVec sz s)) * kᵀ
      = (k * diagonal fun p => (scaleVec sz s p)⁻¹) * lower sz X *
          (diagonal (scaleVec sz s) * kᵀ) := by simp only [Matrix.mul_assoc]
    _ = ((diagonal fun p => (scaleVec sz s p)⁻¹) * k) * lower sz X *
          (kᵀ * diagonal (scaleVec sz s)) := by rw [h1, h2]
    _ = (diagonal fun p => (scaleVec sz s p)⁻¹) * (k * lower sz X * kᵀ) *
          diagonal (scaleVec sz s) := by simp only [Matrix.mul_assoc]

theorem mem_blockOrth_iff {g : Langlands.GeneralLinear (∑ i, sz i) ℝ} :
    g ∈ blockOrth sz ↔ (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) *
        (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)ᵀ = 1 ∧
      BlockZero sz (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) :=
  Iff.rfl

theorem transpose_mul_self_of_mem_unitaryCompact {N : ℕ} {g : Langlands.GeneralLinear N ℝ}
    (hg : g ∈ unitaryCompact ℝ N) :
    (g : Matrix (Fin N) (Fin N) ℝ)ᵀ * (g : Matrix (Fin N) (Fin N) ℝ) = 1 := by
  have h := (mem_unitaryCompact_iff ℝ N g).mp hg
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h

theorem mem_blockOrth_of_mem_unitaryCompact {g : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hg : g ∈ unitaryCompact ℝ (∑ i, sz i))
    (hz : BlockZero sz (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)) : g ∈ blockOrth sz :=
  ⟨mul_eq_one_comm.mp (transpose_mul_self_of_mem_unitaryCompact hg), hz⟩

theorem mem_unitaryCompact_of_mem_blockOrth {g : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hg : g ∈ blockOrth sz) : g ∈ unitaryCompact ℝ (∑ i, sz i) := by
  rw [mem_unitaryCompact_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  exact transpose_mul_self_of_mem hg

/-- The rotation `r_p(θ)` in the coordinates `p, p + 1` of one block is block orthogonal. -/
theorem blockRotation_mem_blockOrth {p : ℕ} (h : p + 1 < ∑ i, sz i)
    (hcls : cls sz ⟨p, by omega⟩ = cls sz ⟨p + 1, h⟩) (θ : ℝ) :
    blockRotation (∑ i, sz i) p θ ∈ blockOrth sz := by
  refine mem_blockOrth_of_mem_unitaryCompact (blockRotation_mem_unitaryCompact _ p θ)
    fun i j hij => ?_
  rw [RealBlockRotation.blockRotation_apply h]
  have hi1 : ∀ i : Fin (∑ i, sz i), (i : ℕ) = p + 1 → i = ⟨p + 1, h⟩ := fun i hi => Fin.ext hi
  have hi0 : ∀ i : Fin (∑ i, sz i), (i : ℕ) = p → i = ⟨p, by omega⟩ := fun i hi => Fin.ext hi
  split_ifs with h1 h2 h3 h4
  · exact absurd (by rw [hi1 i h1.1, hi0 j h1.2, hcls]) hij
  · exact absurd (by rw [hi0 i h2.1, hi1 j h2.2, hcls]) hij
  · exact absurd (congrArg (cls sz) h3.1) hij
  · exact absurd (congrArg (cls sz) h4) hij
  · rfl

theorem blockDiagHom_transpose (A : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    (blockDiagHom sz A)ᵀ = blockDiagHom sz fun i => (A i)ᵀ := by
  rw [blockDiagHom_apply, blockDiagHom_apply, Matrix.transpose_reindex,
    Matrix.blockDiagonal'_transpose]

theorem blockZero_blockDiagHom (A : ∀ i, Matrix (Fin (sz i)) (Fin (sz i)) ℝ) :
    BlockZero sz (blockDiagHom sz A) := by
  intro p q hpq
  obtain ⟨a, ha⟩ := pos_cls sz p
  obtain ⟨b, hb⟩ := pos_cls sz q
  rw [← ha, ← hb]
  exact blockDiagHom_pos_pos_of_ne sz A hpq a b

/-- Block diagonal orthogonal matrices `diag(κ_0, …, κ_{c-1})` are block orthogonal. -/
theorem blockDiagGL_mem_blockOrth (κ : ∀ i, unitaryCompact ℝ (sz i)) :
    blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)) ∈ blockOrth sz := by
  refine ⟨?_, ?_⟩
  · rw [blockDiagGL_val, blockDiagHom_transpose, ← map_mul]
    have : ((fun i => ((κ i : Langlands.GeneralLinear (sz i) ℝ) :
        Matrix (Fin (sz i)) (Fin (sz i)) ℝ)) * fun i => ((κ i : Langlands.GeneralLinear (sz i) ℝ) :
          Matrix (Fin (sz i)) (Fin (sz i)) ℝ)ᵀ) = 1 :=
      funext fun i => mul_eq_one_comm.mp (transpose_mul_self_of_mem_unitaryCompact (κ i).2)
    rw [this, map_one]
  · rw [blockDiagGL_val]
    exact blockZero_blockDiagHom _

theorem blockDiagGL_mem_unitaryCompact (κ : ∀ i, unitaryCompact ℝ (sz i)) :
    blockDiagGL sz (fun i => (κ i : Langlands.GeneralLinear (sz i) ℝ)) ∈
      unitaryCompact ℝ (∑ i, sz i) :=
  mem_unitaryCompact_of_mem_blockOrth (blockDiagGL_mem_blockOrth κ)

end BlockOrth

/-! ## `Ad(k)` preserves Lebesgue measure -/

section Measure

variable {c : ℕ} {sz : Fin c → ℕ}

/-- The strictly lower block part `n̄(X) - 1`. -/
def strict (X : Coord sz → ℝ) : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ :=
  Matrix.of fun p q => if h : cls sz q < cls sz p then X ⟨(p, q), h⟩ else 0

theorem lower_eq_strict_add_one (X : Coord sz → ℝ) : lower sz X = strict X + 1 := by
  ext p q
  simp only [lower, strict, Matrix.of_apply, Matrix.add_apply, Matrix.one_apply]
  by_cases h : cls sz q < cls sz p
  · have hpq : p ≠ q := fun e => h.ne' (congrArg (cls sz) e)
    simp [h, hpq]
  · simp [h]

theorem strict_apply_of_not_lt (X : Coord sz → ℝ) {p q : Fin (∑ i, sz i)}
    (h : ¬ cls sz q < cls sz p) : strict X p q = 0 := by
  simp [strict, h]

theorem strict_apply_coord (X : Coord sz → ℝ) (pq : Coord sz) : strict X pq.1.1 pq.1.2 = X pq := by
  simp [strict, pq.2]

theorem adCoord_eq {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ} (hk : k * kᵀ = 1)
    (X : Coord sz → ℝ) (pq : Coord sz) : adCoord k X pq = (k * strict X * kᵀ) pq.1.1 pq.1.2 := by
  have hne : pq.1.1 ≠ pq.1.2 := fun e => pq.2.ne' (congrArg (cls sz) e)
  rw [adCoord, lower_eq_strict_add_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hk,
    Matrix.add_apply, Matrix.one_apply_ne hne, add_zero]

/-- `X ↦ k (n̄(X) - 1) kᵀ` in coordinates, as a linear map. -/
def adLin (k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) :
    (Coord sz → ℝ) →ₗ[ℝ] (Coord sz → ℝ) where
  toFun X pq := (k * strict X * kᵀ) pq.1.1 pq.1.2
  map_add' X Y := by
    funext pq
    have : strict (X + Y) = strict X + strict Y := by
      ext p q
      simp only [strict, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
      split_ifs <;> simp
    simp only [this, Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, Pi.add_apply]
  map_smul' a X := by
    funext pq
    have : strict (a • X) = a • strict X := by
      ext p q
      simp only [strict, Matrix.of_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
      split_ifs <;> simp
    simp only [this, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, Pi.smul_apply,
      RingHom.id_apply, smul_eq_mul]

theorem adLin_apply {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ} (hk : k * kᵀ = 1)
    (X : Coord sz → ℝ) : adLin k X = adCoord k X :=
  funext fun pq => (adCoord_eq hk X pq).symm

theorem sum_coord_sq {M : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ}
    (hM : ∀ p q, ¬ cls sz q < cls sz p → M p q = 0) :
    ∑ pq : Coord sz, M pq.1.1 pq.1.2 ^ 2 = ∑ p, ∑ q, M p q ^ 2 := by
  calc ∑ pq : Coord sz, M pq.1.1 pq.1.2 ^ 2
      = ∑ pq : Coord sz, M pq.1.1 pq.1.2 ^ 2 +
          ∑ pq : {x : Fin (∑ i, sz i) × Fin (∑ i, sz i) // ¬ cls sz x.2 < cls sz x.1},
            M pq.1.1 pq.1.2 ^ 2 := by
        have h0 : ∑ pq : {x : Fin (∑ i, sz i) × Fin (∑ i, sz i) // ¬ cls sz x.2 < cls sz x.1},
            M pq.1.1 pq.1.2 ^ 2 = 0 :=
          Finset.sum_eq_zero fun pq _ => by simp [hM _ _ pq.2]
        rw [h0, add_zero]
    _ = ∑ x : Fin (∑ i, sz i) × Fin (∑ i, sz i), M x.1 x.2 ^ 2 :=
        Fintype.sum_subtype_add_sum_subtype (fun x => cls sz x.2 < cls sz x.1)
          (fun x : Fin (∑ i, sz i) × Fin (∑ i, sz i) => M x.1 x.2 ^ 2)
    _ = ∑ p, ∑ q, M p q ^ 2 := Fintype.sum_prod_type' fun p q => M p q ^ 2

theorem sum_sq_conj {N : ℕ} {k : Matrix (Fin N) (Fin N) ℝ} (hk : kᵀ * k = 1)
    (S : Matrix (Fin N) (Fin N) ℝ) :
    ∑ p, ∑ q, (k * S * kᵀ) p q ^ 2 = ∑ p, ∑ q, S p q ^ 2 := by
  have key : ∀ M : Matrix (Fin N) (Fin N) ℝ, ∑ p, ∑ q, M p q ^ 2 = (M * Mᵀ).trace := by
    intro M
    simp [Matrix.trace, Matrix.mul_apply, sq]
  have e : k * S * kᵀ * (k * S * kᵀ)ᵀ = k * (S * Sᵀ) * kᵀ := by
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc kᵀ k, hk, Matrix.one_mul]
  rw [key, key, e, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hk, Matrix.one_mul]

theorem sum_sq_adCoord {k : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ} (hk : k * kᵀ = 1)
    (hz : BlockZero sz k) (X : Coord sz → ℝ) :
    ∑ pq, adCoord k X pq ^ 2 = ∑ pq, X pq ^ 2 := by
  have hS' : ∀ p q, ¬ cls sz q < cls sz p → (k * strict X * kᵀ) p q = 0 := by
    intro p q h
    have e := lower_conj_apply_of_not_lt hk hz X h
    rw [lower_eq_strict_add_one, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hk,
      Matrix.add_apply] at e
    linarith
  calc ∑ pq, adCoord k X pq ^ 2 = ∑ pq : Coord sz, (k * strict X * kᵀ) pq.1.1 pq.1.2 ^ 2 :=
        Finset.sum_congr rfl fun pq _ => by rw [adCoord_eq hk]
    _ = ∑ p, ∑ q, (k * strict X * kᵀ) p q ^ 2 := sum_coord_sq hS'
    _ = ∑ p, ∑ q, strict X p q ^ 2 := sum_sq_conj (mul_eq_one_comm.mp hk) _
    _ = ∑ pq : Coord sz, strict X pq.1.1 pq.1.2 ^ 2 :=
        (sum_coord_sq fun p q h => strict_apply_of_not_lt X h).symm
    _ = ∑ pq, X pq ^ 2 := Finset.sum_congr rfl fun pq _ => by rw [strict_apply_coord]

/-- `Ad(k)` preserves Lebesgue measure on the coordinates of `N̄_Q`, for block orthogonal `k`. -/
theorem measurePreserving_adCoord {g : Langlands.GeneralLinear (∑ i, sz i) ℝ}
    (hg : g ∈ blockOrth sz) :
    MeasurePreserving (adCoord (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) (sz := sz))
      volume volume := by
  set k := (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ)
  have hk : k * kᵀ = 1 := hg.1
  let f : EuclideanSpace ℝ (Coord sz) →ₗ[ℝ] EuclideanSpace ℝ (Coord sz) :=
    (WithLp.linearEquiv 2 ℝ (Coord sz → ℝ)).symm.toLinearMap ∘ₗ adLin k ∘ₗ
      (WithLp.linearEquiv 2 ℝ (Coord sz → ℝ)).toLinearMap
  have hf : ∀ x, f x = WithLp.toLp 2 (adCoord k (WithLp.ofLp x)) := by
    intro x
    simp only [f, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      WithLp.coe_linearEquiv, WithLp.coe_symm_linearEquiv]
    rw [adLin_apply hk]
  have hnorm : ∀ x, ‖f x‖ = ‖x‖ := by
    intro x
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, hf]
    congr 1
    simp only [Real.norm_eq_abs, sq_abs]
    exact sum_sq_adCoord hg.1 hg.2 _
  let li : EuclideanSpace ℝ (Coord sz) →ₗᵢ[ℝ] EuclideanSpace ℝ (Coord sz) := ⟨f, hnorm⟩
  have hmp := (li.toLinearIsometryEquiv rfl).measurePreserving
  have e : adCoord k = WithLp.ofLp ∘ (li.toLinearIsometryEquiv rfl) ∘ WithLp.toLp 2 := by
    funext X
    simp only [Function.comp_apply, LinearIsometry.coe_toLinearIsometryEquiv]
    change adCoord k X = WithLp.ofLp (f (WithLp.toLp 2 X))
    rw [hf]
  rw [e]
  exact (PiLp.volume_preserving_ofLp _).comp (hmp.comp (PiLp.volume_preserving_toLp _))

end Measure

end RealLeviChart

open RealLeviChart GramFormula in
/-- **Geometry of `N̄_Q`.** For every standard parabolic subgroup `Q` of `GL_N(ℝ)` with block sizes
`sz`: the Gram determinants of `n̄(X)` are `≥ 1` and do not increase under the scaling
`X ↦ X_s` for `s ≥ 1`; `n̄(X) d_s = d_s n̄(X_s)`; every block orthogonal `g` satisfies
`g n̄(X) = n̄(Ad(g) X) g`, and `Ad(g)` preserves Lebesgue measure and commutes with the scaling. -/
def RealLeviGeometryStatement : Prop :=
  ∀ (c : ℕ) (sz : Fin c → ℕ),
    (∀ (X : Coord sz → ℝ) (l : ℕ), 1 ≤ gram l (lower sz X)) ∧
    (∀ s : ℝ, 1 ≤ s → ∀ (X : Coord sz → ℝ) (l : ℕ),
      gram l (lower sz (scaleCoord sz s X)) ≤ gram l (lower sz X)) ∧
    (∀ (s : ℝ) (hs : 0 < s) (X : Coord sz → ℝ),
      lowerGL sz X * scaleGL sz hs = scaleGL sz hs * lowerGL sz (scaleCoord sz s X)) ∧
    (∀ g ∈ blockOrth sz, ∀ X : Coord sz → ℝ,
      g * lowerGL sz X = lowerGL sz (adCoord (g : Matrix _ _ ℝ) X) * g) ∧
    (∀ g ∈ blockOrth sz,
      MeasurePreserving (adCoord (g : Matrix (Fin (∑ i, sz i)) (Fin (∑ i, sz i)) ℝ) (sz := sz))
        volume volume) ∧
    (∀ g ∈ blockOrth sz, ∀ (s : ℝ), 0 < s → ∀ X : Coord sz → ℝ,
      adCoord (g : Matrix _ _ ℝ) (scaleCoord sz s X) =
        scaleCoord sz s (adCoord (g : Matrix _ _ ℝ) X))

open RealLeviChart in
theorem realLeviGeometry : RealLeviGeometryStatement := fun _ sz =>
  ⟨one_le_gram_lower sz, fun _ hs => gram_lower_scaleCoord_le sz hs,
    fun _ hs => lowerGL_mul_scaleGL sz hs, fun _ hg => mul_lowerGL hg,
    fun _ hg => measurePreserving_adCoord hg,
    fun _ hg _ hs => adCoord_scaleCoord hg.1 hg.2 hs⟩

end Langlands.Archimedean
