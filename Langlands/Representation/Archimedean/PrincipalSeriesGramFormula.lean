import Langlands.Representation.Archimedean.OrthogonalFinitePolynomial
import Langlands.Representation.Archimedean.RealStandardModuleAdmissible

/-!
# `O(n)`-finite principal-series functions as Gram-determinant expressions
-/

noncomputable section

open Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

namespace GramFormula

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

/-! ## Gram determinants over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The Gram matrix `x xᵀ` of the rows of `x` on the rows and columns `≥ i`, padded by the
identity matrix on the other rows and columns. -/
def paddedGram (i : ℕ) (x : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun p q =>
    if i ≤ (p : ℕ) ∧ i ≤ (q : ℕ) then (x * xᵀ) p q else (1 : Matrix (Fin n) (Fin n) R) p q

/-- The Gram determinant of the rows `i, …, n-1` of `x`. -/
def gram (i : ℕ) (x : Matrix (Fin n) (Fin n) R) : R :=
  (paddedGram i x).det

/-- The `j`-th column of `x` on the rows `≥ i`, and `0` on the other rows. -/
def gramColumnVector (i j : Fin n) (x : Matrix (Fin n) (Fin n) R) : Fin n → R :=
  fun p => if (i : ℕ) ≤ (p : ℕ) then x p j else 0

/-- The determinant of the padded Gram matrix of the rows `≥ i` with its `i`-th column replaced
by the `j`-th column of `x`. -/
def gramColumn (i j : Fin n) (x : Matrix (Fin n) (Fin n) R) : R :=
  ((paddedGram i x).updateCol i (gramColumnVector i j x)).det

theorem paddedGram_map {S : Type*} [CommRing S] (φ : R →+* S) (i : ℕ)
    (x : Matrix (Fin n) (Fin n) R) :
    paddedGram i (x.map φ) = (paddedGram i x).map φ := by
  ext p q
  simp only [paddedGram, Matrix.of_apply, Matrix.map_apply]
  split_ifs
  · rw [← Matrix.transpose_map, ← Matrix.map_mul, Matrix.map_apply]
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem gram_map {S : Type*} [CommRing S] (φ : R →+* S) (i : ℕ)
    (x : Matrix (Fin n) (Fin n) R) : gram i (x.map φ) = φ (gram i x) := by
  rw [gram, gram, paddedGram_map, RingHom.map_det]
  rfl

theorem gramColumn_map {S : Type*} [CommRing S] (φ : R →+* S) (i j : Fin n)
    (x : Matrix (Fin n) (Fin n) R) : gramColumn i j (x.map φ) = φ (gramColumn i j x) := by
  have hv : gramColumnVector i j (x.map φ) = φ ∘ gramColumnVector i j x := by
    funext p
    simp only [gramColumnVector, Function.comp_apply, Matrix.map_apply]
    split_ifs <;> simp
  rw [gramColumn, gramColumn, paddedGram_map, hv, ← Matrix.map_updateCol, RingHom.map_det]
  rfl

/-! ## Gram determinants of `b κ` with `b` upper triangular and `κ` orthogonal -/

/-- `b` on the rows and columns `≥ i`, padded by the identity matrix. -/
def padded (i : ℕ) (b : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun p q =>
    if i ≤ (p : ℕ) ∧ i ≤ (q : ℕ) then b p q else (1 : Matrix (Fin n) (Fin n) R) p q

variable {b κ : Matrix (Fin n) (Fin n) R}

theorem padded_apply_of_le (hb : b.IsUpperTriangular) {i : ℕ} {p : Fin n} (hp : i ≤ (p : ℕ))
    (q : Fin n) : padded i b p q = b p q := by
  simp only [padded, Matrix.of_apply]
  split_ifs with h
  · rfl
  · have hqp : q < p := by
      rw [Fin.lt_def]
      have : ¬ i ≤ (q : ℕ) := fun hq => h ⟨hp, hq⟩
      omega
    rw [hb hqp, Matrix.one_apply_ne (ne_of_gt hqp)]

theorem padded_apply_of_lt (b : Matrix (Fin n) (Fin n) R) {i : ℕ} {p : Fin n}
    (hp : (p : ℕ) < i) (q : Fin n) : padded i b p q = (1 : Matrix (Fin n) (Fin n) R) p q := by
  simp only [padded, Matrix.of_apply]
  rw [ite_eq_right (fun h => absurd h.1 (by omega))]

theorem padded_isUpperTriangular (hb : b.IsUpperTriangular) (i : ℕ) :
    (padded i b).IsUpperTriangular := by
  intro p q hqp
  by_cases hp : i ≤ (p : ℕ)
  · rw [padded_apply_of_le hb hp]
    exact hb hqp
  · rw [padded_apply_of_lt b (by omega)]
    exact Matrix.one_apply_ne (ne_of_gt hqp)

/-- The product of the diagonal entries of `b` in the positions `≥ i`. -/
def diagonalTail (i : ℕ) (b : Matrix (Fin n) (Fin n) R) : R :=
  ∏ l : Fin n, if i ≤ (l : ℕ) then b l l else 1

theorem det_padded (hb : b.IsUpperTriangular) (i : ℕ) :
    (padded i b).det = diagonalTail i b := by
  rw [Matrix.det_of_isUpperTriangular (padded_isUpperTriangular hb i), diagonalTail]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs with h
  · exact padded_apply_of_le hb h l
  · rw [padded_apply_of_lt b (by omega), Matrix.one_apply_eq]

theorem diagonalTail_succ (b : Matrix (Fin n) (Fin n) R) (i : Fin n) :
    diagonalTail (i : ℕ) b = b i i * diagonalTail ((i : ℕ) + 1) b := by
  rw [diagonalTail, diagonalTail]
  have h : ∀ l : Fin n, (if (i : ℕ) ≤ (l : ℕ) then b l l else 1) =
      (if l = i then b l l else 1) * (if (i : ℕ) + 1 ≤ (l : ℕ) then b l l else 1) := by
    intro l
    by_cases hl : l = i
    · subst hl
      simp
    · have : (l : ℕ) ≠ (i : ℕ) := fun h => hl (Fin.ext h)
      by_cases h1 : (i : ℕ) ≤ (l : ℕ)
      · rw [ite_eq_left h1, ite_eq_right hl, ite_eq_left (by omega), one_mul]
      · rw [ite_eq_right h1, ite_eq_right hl, ite_eq_right (by omega), one_mul]
  rw [Finset.prod_congr rfl fun l _ => h l, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem row_padded_of_le (hb : b.IsUpperTriangular) {i : ℕ} {p : Fin n} (hp : i ≤ (p : ℕ)) :
    padded i b p = b p :=
  funext fun q => padded_apply_of_le hb hp q

theorem row_padded_of_lt (b : Matrix (Fin n) (Fin n) R) {i : ℕ} {p : Fin n}
    (hp : (p : ℕ) < i) : padded i b p = Pi.single p 1 := by
  funext q
  rw [padded_apply_of_lt b hp, Matrix.one_apply, Pi.single_apply]
  by_cases h : p = q
  · subst h
    simp
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

theorem mul_mul_transpose (hκ : κ * κᵀ = 1) : (b * κ) * (b * κ)ᵀ = b * bᵀ := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κ, hκ, Matrix.one_mul]

theorem paddedGram_mul (hb : b.IsUpperTriangular) (hκ : κ * κᵀ = 1) (i : ℕ) :
    paddedGram i (b * κ) = padded i b * (padded i b)ᵀ := by
  ext p q
  rw [Matrix.mul_apply']
  simp only [paddedGram, Matrix.of_apply, mul_mul_transpose hκ, Matrix.transpose_apply]
  change _ = padded i b p ⬝ᵥ padded i b q
  by_cases hp : i ≤ (p : ℕ)
  · by_cases hq : i ≤ (q : ℕ)
    · rw [ite_eq_left ⟨hp, hq⟩, row_padded_of_le hb hp, row_padded_of_le hb hq, Matrix.mul_apply']
      rfl
    · have hqp : q < p := by rw [Fin.lt_def]; omega
      rw [ite_eq_right (fun h => hq h.2), row_padded_of_le hb hp, row_padded_of_lt b (by omega),
        dotProduct_single, mul_one, hb hqp, Matrix.one_apply_ne (ne_of_gt hqp)]
  · rw [ite_eq_right (fun h => hp h.1), row_padded_of_lt b (by omega), single_dotProduct, one_mul]
    by_cases hq : i ≤ (q : ℕ)
    · have hpq : p < q := by rw [Fin.lt_def]; omega
      rw [row_padded_of_le hb hq, hb hpq, Matrix.one_apply_ne (ne_of_lt hpq)]
    · rw [row_padded_of_lt b (by omega), Pi.single_apply, Matrix.one_apply]

theorem gram_mul (hb : b.IsUpperTriangular) (hκ : κ * κᵀ = 1) (i : ℕ) :
    gram i (b * κ) = diagonalTail i b ^ 2 := by
  rw [gram, paddedGram_mul hb hκ, Matrix.det_mul, Matrix.det_transpose, det_padded hb, sq]

/-- The lower triangular factor in `gramColumn_mul`. -/
def columnFactor (i j : Fin n) (b κ : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun l q =>
    if (q : ℕ) < i ∨ (l : ℕ) < i then (1 : Matrix (Fin n) (Fin n) R) l q
    else if q = i then κ l j else b q l

theorem columnFactor_isLowerTriangular (hb : b.IsUpperTriangular) (i j : Fin n) :
    (columnFactor i j b κ).IsLowerTriangular := by
  intro l q hlq
  change l < q at hlq
  simp only [columnFactor, Matrix.of_apply]
  split_ifs with h1 h2
  · exact Matrix.one_apply_ne (ne_of_lt hlq)
  · subst h2
    exact absurd (Fin.lt_def.mp hlq) (by omega)
  · exact hb hlq

theorem det_columnFactor (hb : b.IsUpperTriangular) (i j : Fin n) :
    (columnFactor i j b κ).det = κ i j * diagonalTail ((i : ℕ) + 1) b := by
  rw [Matrix.det_of_isLowerTriangular _ (columnFactor_isLowerTriangular hb i j), diagonalTail]
  have h : ∀ l : Fin n, columnFactor i j b κ l l =
      (if l = i then κ i j else 1) * (if (i : ℕ) + 1 ≤ (l : ℕ) then b l l else 1) := by
    intro l
    simp only [columnFactor, Matrix.of_apply]
    by_cases hl : l = i
    · subst hl
      simp
    · have : (l : ℕ) ≠ (i : ℕ) := fun h => hl (Fin.ext h)
      by_cases h1 : (l : ℕ) < (i : ℕ)
      · rw [ite_eq_left (Or.inl h1), ite_eq_right hl, ite_eq_right (by omega), Matrix.one_apply_eq, one_mul]
      · rw [ite_eq_right (by omega), ite_eq_right hl, ite_eq_right hl, ite_eq_left (by omega), one_mul]
  rw [Finset.prod_congr rfl fun l _ => h l, Finset.prod_mul_distrib, Finset.prod_ite_eq']
  simp

theorem updateCol_paddedGram_mul (hb : b.IsUpperTriangular) (hκ : κ * κᵀ = 1) (i j : Fin n) :
    (paddedGram i (b * κ)).updateCol i (gramColumnVector i j (b * κ)) =
      padded i b * columnFactor i j b κ := by
  ext p q
  rw [Matrix.updateCol_apply, Matrix.mul_apply]
  by_cases hp : (i : ℕ) ≤ (p : ℕ)
  · simp only [row_padded_of_le hb hp]
    by_cases hqi : q = i
    · subst hqi
      rw [ite_eq_left rfl, gramColumnVector, ite_eq_left hp, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [columnFactor, Matrix.of_apply]
      by_cases hl : (l : ℕ) < (q : ℕ)
      · have hlp : l < p := by rw [Fin.lt_def]; omega
        rw [hb hlp, zero_mul, zero_mul]
      · rw [ite_eq_right (by omega)]
        simp
    · rw [ite_eq_right hqi]
      simp only [paddedGram, Matrix.of_apply, mul_mul_transpose hκ]
      by_cases hq : (q : ℕ) < (i : ℕ)
      · have hqp : q < p := by rw [Fin.lt_def]; omega
        rw [ite_eq_right (fun h => by omega), Matrix.one_apply_ne (ne_of_gt hqp)]
        symm
        refine Finset.sum_eq_zero fun l _ => ?_
        simp only [columnFactor, Matrix.of_apply, ite_eq_left (Or.inl hq), Matrix.one_apply]
        split_ifs with hlq
        · subst hlq
          rw [hb hqp, zero_mul]
        · rw [mul_zero]
      · rw [ite_eq_left ⟨hp, by omega⟩, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun l _ => ?_
        simp only [columnFactor, Matrix.of_apply, Matrix.transpose_apply]
        by_cases hl : (l : ℕ) < (i : ℕ)
        · have hlp : l < p := by rw [Fin.lt_def]; omega
          rw [hb hlp, zero_mul, zero_mul]
        · rw [ite_eq_right (by omega), ite_eq_right hqi]
  · simp only [row_padded_of_lt b (show (p : ℕ) < i by omega), Pi.single_apply]
    rw [Finset.sum_eq_single p (fun l _ hl => by rw [ite_eq_right hl, zero_mul])
      (fun h => absurd (Finset.mem_univ p) h), ite_eq_left rfl, one_mul]
    simp only [columnFactor, Matrix.of_apply, ite_eq_left (Or.inr (show (p : ℕ) < i by omega))]
    by_cases hqi : q = i
    · subst hqi
      rw [ite_eq_left rfl, gramColumnVector, ite_eq_right hp, Matrix.one_apply_ne]
      intro h
      exact hp (h ▸ le_refl _)
    · rw [ite_eq_right hqi]
      simp only [paddedGram, Matrix.of_apply]
      rw [ite_eq_right (fun h => hp h.1)]

theorem gramColumn_mul (hb : b.IsUpperTriangular) (hκ : κ * κᵀ = 1) (i j : Fin n) :
    gramColumn i j (b * κ) =
      diagonalTail (i : ℕ) b * (κ i j * diagonalTail ((i : ℕ) + 1) b) := by
  rw [gramColumn, updateCol_paddedGram_mul hb hκ, Matrix.det_mul, det_padded hb,
    det_columnFactor hb]

end Ring

/-! ## Real matrices -/

/-- For `r ≠ 0`, `(r²)^(c/2) = |r|^c` with the principal branch. -/
theorem ofReal_sq_cpow_half {r : ℝ} (hr : r ≠ 0) (c : ℂ) :
    ((r ^ 2 : ℝ) : ℂ) ^ (c / 2) = ((|r| : ℝ) : ℂ) ^ c := by
  have h1 : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast pow_ne_zero 2 hr
  have h2 : ((|r| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr hr
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2,
    ← Complex.ofReal_log (sq_nonneg r), ← Complex.ofReal_log (abs_nonneg r)]
  congr 1
  rw [show r ^ 2 = |r| ^ 2 from (sq_abs r).symm, Real.log_pow]
  push_cast
  ring

/-- The sign `±1` of a real number (`-1` for `0`). -/
def signReal (r : ℝ) : ℝ := if 0 < r then 1 else -1

theorem abs_signReal (r : ℝ) : |signReal r| = 1 := by
  unfold signReal
  split_ifs <;> simp

theorem mul_inv_abs_eq_signReal {d : ℝ} (hd : d ≠ 0) : d * (|d|)⁻¹ = signReal d := by
  rcases lt_or_gt_of_ne hd with h | h
  · rw [signReal, ite_eq_right (not_lt.mpr h.le), abs_of_neg h, inv_neg, mul_neg,
      mul_inv_cancel₀ hd]
  · rw [signReal, ite_eq_left h, abs_of_pos h, mul_inv_cancel₀ hd]

theorem mul_mul_inv_abs {d q : ℝ} (hd : d ≠ 0) (hq : q ≠ 0) (k : ℝ) :
    d * q * (k * q) * (|d * q|)⁻¹ * (|q|)⁻¹ = signReal d * k := by
  rw [abs_mul, mul_inv]
  have hq2 : q * q * ((|q|)⁻¹ * (|q|)⁻¹) = 1 := by
    rw [← mul_inv, abs_mul_abs_self, mul_inv_cancel₀ (mul_ne_zero hq hq)]
  calc d * q * (k * q) * ((|d|)⁻¹ * (|q|)⁻¹) * (|q|)⁻¹
      = (d * (|d|)⁻¹) * k * (q * q * ((|q|)⁻¹ * (|q|)⁻¹)) := by ring
    _ = signReal d * k := by rw [hq2, mul_inv_abs_eq_signReal hd, mul_one]

variable {n : ℕ}

/-- A real matrix as a complex matrix. -/
abbrev complexify (x : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  x.map Complex.ofRealHom

/-- The Gram expression of exponents `s` and a polynomial `P` at a complex matrix `Z`:
`∏ₗ G_l^(s_l/2) G_{l+1}^(-s_l/2) · P(κ̂)`, with `G_l = gram l Z` and
`κ̂_ij = gramColumn i j Z · G_i^(-1/2) G_{i+1}^(-1/2)`, all powers principal. -/
def gramExpression (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (Z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (∏ l : Fin n, gram (l : ℕ) Z ^ (s l / 2) * gram ((l : ℕ) + 1) Z ^ (-(s l / 2))) *
    MvPolynomial.eval (fun ij : Fin n × Fin n =>
      gramColumn ij.1 ij.2 Z * gram (ij.1 : ℕ) Z ^ (-(1 / 2 : ℂ)) *
        gram ((ij.1 : ℕ) + 1) Z ^ (-(1 / 2 : ℂ))) P

theorem diagonalTail_ne_zero {b : Matrix (Fin n) (Fin n) ℝ} (hd : ∀ l, b l l ≠ 0) (i : ℕ) :
    diagonalTail i b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun l _ => by
    split_ifs
    exacts [hd l, one_ne_zero]

/-- The Gram expression at `b κ`, with `b` upper triangular with nonzero diagonal and `κ`
orthogonal. -/
theorem gramExpression_complexify_mul {b κ : Matrix (Fin n) (Fin n) ℝ}
    (hb : b.IsUpperTriangular) (hd : ∀ l, b l l ≠ 0) (hκ : κ * κᵀ = 1)
    (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ) :
    gramExpression s P (complexify (b * κ)) =
      (∏ l : Fin n, ((|b l l| : ℝ) : ℂ) ^ s l) *
        MvPolynomial.eval (fun ij : Fin n × Fin n =>
          ((signReal (b ij.1 ij.1) * κ ij.1 ij.2 : ℝ) : ℂ)) P := by
  have hT := diagonalTail_ne_zero hd
  have hG : ∀ i : ℕ, gram i (complexify (b * κ)) = ((diagonalTail i b ^ 2 : ℝ) : ℂ) :=
    fun i => by
      rw [complexify, gram_map, gram_mul hb hκ]
      rfl
  have hC : ∀ i j : Fin n, gramColumn i j (complexify (b * κ)) =
      ((diagonalTail (i : ℕ) b * (κ i j * diagonalTail ((i : ℕ) + 1) b) : ℝ) : ℂ) :=
    fun i j => by
      rw [complexify, gramColumn_map, gramColumn_mul hb hκ]
      rfl
  unfold gramExpression
  congr 1
  · refine Finset.prod_congr rfl fun l _ => ?_
    have hne : ((|diagonalTail ((l : ℕ) + 1) b| : ℝ) : ℂ) ^ s l ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast abs_ne_zero.mpr (hT _)))
    rw [hG, hG, diagonalTail_succ b l, ofReal_sq_cpow_half (mul_ne_zero (hd l) (hT _)),
      show -(s l / 2) = -s l / 2 by ring, ofReal_sq_cpow_half (hT _), abs_mul,
      Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (abs_nonneg _),
      Complex.cpow_neg, mul_assoc, mul_inv_cancel₀ hne, mul_one]
  · refine congrArg (fun v => MvPolynomial.eval v P) (funext fun ij => ?_)
    rw [hC, hG, hG, show (-(1 / 2 : ℂ)) = (-1) / 2 by ring, ofReal_sq_cpow_half (hT _),
      ofReal_sq_cpow_half (hT _), Complex.cpow_neg_one, Complex.cpow_neg_one,
      diagonalTail_succ b ij.1, ← Complex.ofReal_inv, ← Complex.ofReal_inv,
      ← Complex.ofReal_mul, ← Complex.ofReal_mul, mul_mul_inv_abs (hd _) (hT _)]

/-! ## `O(n)`-finite principal-series functions -/

/-- The sign `±1` of a real unit, as a unit. -/
def signUnit (x : ℝˣ) : ℝˣ := if (0 : ℝ) < (x : ℝ) then 1 else -1

theorem signUnit_val (x : ℝˣ) : ((signUnit x : ℝˣ) : ℝ) = signReal x := by
  unfold signUnit signReal
  split_ifs <;> simp

/-- The exponents `e_l + (n - 1)/2 - l` of the absolute values in the principal series. -/
def shiftedExponent (n : ℕ) (e : ℕ → ℂ) (l : Fin n) : ℂ :=
  e l + (((n : ℂ) - 1) / 2 - ((l : ℕ) : ℂ))

theorem principalSeriesCharacter_eq {χ : ℕ → ℝˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l)
    (a : Fin n → ℝˣ) :
    principalSeriesCharacter ℝ n χ a =
      (∏ l : Fin n, ((|(a l : ℝ)| : ℝ) : ℂ) ^ shiftedExponent n e l) *
        principalSeriesCharacter ℝ n χ (fun l => signUnit (a l)) := by
  simp only [principalSeriesCharacter, Module.finrank_self, pow_one, Real.norm_eq_abs,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ha : ((|(a l : ℝ)| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.mpr (a l).ne_zero
  rw [hχ l (a l), signUnit_val, abs_signReal, Complex.ofReal_one, Complex.one_cpow, mul_one,
    shiftedExponent, Complex.cpow_add _ _ ha]
  ring

theorem diagonalUnits_signUnit_mem (a : Fin n → ℝˣ) :
    (Iwasawa.diagonalUnits (fun l => signUnit (a l)) : Langlands.GeneralLinear n ℝ) ∈
      unitaryCompact ℝ n := by
  change (Matrix.diagonal fun l => ((signUnit (a l) : ℝˣ) : ℝ)) ∈ Matrix.unitaryGroup (Fin n) ℝ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext l
  simp only [Pi.star_apply, star_trivial, signUnit_val]
  unfold signReal
  split_ifs <;> norm_num

theorem isUpperTriangular_diagonal_mul (a : Fin n → ℝˣ) (u : upperUnipotent n ℝ) :
    (Matrix.diagonal (fun l => (a l : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)).IsUpperTriangular :=
  (Matrix.blockTriangular_diagonal _).mul u.property.1

theorem diagonal_mul_apply_self (a : Fin n → ℝˣ) (u : upperUnipotent n ℝ) (l : Fin n) :
    (Matrix.diagonal (fun l => (a l : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) l l = a l := by
  rw [Matrix.diagonal_mul, u.property.2 l, mul_one]

theorem mul_transpose_eq_one_of_mem {k : Langlands.GeneralLinear n ℝ}
    (hk : k ∈ unitaryCompact ℝ n) :
    (k : Matrix (Fin n) (Fin n) ℝ) * (k : Matrix (Fin n) (Fin n) ℝ)ᵀ = 1 := by
  have := Matrix.mem_unitaryGroup_iff.mp hk
  rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at this

/-- The Gram determinants of an invertible real matrix are positive. -/
theorem gram_pos (x : Langlands.GeneralLinear n ℝ) (i : ℕ) :
    0 < gram i (x : Matrix (Fin n) (Fin n) ℝ) := by
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact x
  have hd : ∀ l, (Matrix.diagonal (fun l => (a l : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) l l ≠ 0 := fun l => by
    rw [diagonal_mul_apply_self]
    exact (a l).ne_zero
  change 0 < gram i ((Matrix.diagonal (fun l => (a l : ℝ)) *
      ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)) *
        (k : Matrix (Fin n) (Fin n) ℝ))
  rw [gram_mul (isUpperTriangular_diagonal_mul a u) (mul_transpose_eq_one_of_mem hk)]
  exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (diagonalTail_ne_zero hd i)))

/-- **Gram formula.** Let the characters satisfy `χ_l(x) = χ_l(sgn x) |x|^(e_l)`. Every
`O(n)`-finite function `f` of the principal series of `χ` is a Gram expression: there is a
polynomial `P` with `f(x) = gramExpression (shiftedExponent n e) P x` for every
`x ∈ GL_n(ℝ)`. -/
theorem exists_gramExpression_eq {χ : ℕ → ℝˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (x : ℝˣ), χ l x = χ l (signUnit x) * ((|(x : ℝ)| : ℝ) : ℂ) ^ e l)
    {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℝ n χ) (unitaryCompact ℝ n)) :
    ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ x : Langlands.GeneralLinear n ℝ,
      f x = gramExpression (shiftedExponent n e) P
        (complexify (x : Matrix (Fin n) (Fin n) ℝ)) := by
  obtain ⟨hps, hK⟩ := Submodule.mem_inf.mp hf
  obtain ⟨P, hP⟩ := OrthogonalFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors
    hps.1.continuous hK 1
  refine ⟨P, fun x => ?_⟩
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact x
  let b : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun l => (a l : ℝ)) *
    ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ)
  have hb : b.IsUpperTriangular := isUpperTriangular_diagonal_mul a u
  have hbd : ∀ l, b l l = a l := diagonal_mul_apply_self a u
  have hd : ∀ l, b l l ≠ 0 := fun l => by rw [hbd]; exact (a l).ne_zero
  have hκ := mul_transpose_eq_one_of_mem hk
  have hx : (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * k : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) = b * (k : Matrix (Fin n) (Fin n) ℝ) := rfl
  rw [hx, gramExpression_complexify_mul hb hd hκ, hps.2 a u k]
  -- the polynomial at the signed matrix
  let y : Langlands.GeneralLinear n ℝ :=
    (Iwasawa.diagonalUnits (fun l => signUnit (a l)) : Langlands.GeneralLinear n ℝ) * k
  have hy : y ∈ unitaryCompact ℝ n := mul_mem (diagonalUnits_signUnit_mem a) hk
  have hPy := hP ⟨(y : Matrix (Fin n) (Fin n) ℝ), hy⟩
  have hyu : Unitary.toUnits (⟨(y : Matrix (Fin n) (Fin n) ℝ), hy⟩ :
      Matrix.unitaryGroup (Fin n) ℝ) = y := Units.ext rfl
  rw [one_mul, hyu] at hPy
  have hfy : f y = principalSeriesCharacter ℝ n χ (fun l => signUnit (a l)) * f k := by
    have := hps.2 (fun l => signUnit (a l)) 1 k
    rwa [OneMemClass.coe_one, mul_one] at this
  have hentries : (fun ij : Fin n × Fin n => ((signReal (b ij.1 ij.1) *
      (k : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ)) =
        fun ij => (((y : Matrix (Fin n) (Fin n) ℝ) ij.1 ij.2 : ℝ) : ℂ) := by
    funext ij
    change _ = (((Matrix.diagonal fun l => ((signUnit (a l) : ℝˣ) : ℝ)) *
      (k : Matrix (Fin n) (Fin n) ℝ)) ij.1 ij.2 : ℂ)
    rw [Matrix.diagonal_mul, signUnit_val, hbd]
  have hprod : (∏ l : Fin n, ((|b l l| : ℝ) : ℂ) ^ shiftedExponent n e l) =
      ∏ l : Fin n, ((|(a l : ℝ)| : ℝ) : ℂ) ^ shiftedExponent n e l :=
    Finset.prod_congr rfl fun l _ => by rw [hbd]
  rw [hentries, ← hPy, hfy, hprod, principalSeriesCharacter_eq e hχ a]
  ring

/-! ## Standard modules -/

/-- The exponent of the absolute value in the character at each diagonal position of a list
of real blocks: `t` for a character `sgn^ε |·|^t`, and `t + |m|/2`, `t - |m|/2` for the two
positions of the real induction of `(z/|z|)^m |z|^(2t)`; `0` past the end. -/
def realPositionExponent : List RealBlock → ℕ → ℂ
  | [], _ => 0
  | .character d :: _, 0 => d.exponent
  | .character _ :: ds, p + 1 => realPositionExponent ds p
  | .induced d :: _, 0 => d.exponent + (d.weight.natAbs : ℂ) / 2
  | .induced d :: _, 1 => d.exponent - (d.weight.natAbs : ℂ) / 2
  | .induced _ :: ds, p + 2 => realPositionExponent ds p

theorem abs_signUnit (x : ℝˣ) : |((signUnit x : ℝˣ) : ℝ)| = 1 := by
  rw [signUnit_val, abs_signReal]

theorem signUnit_div_abs (x : ℝˣ) :
    ((signUnit x : ℝˣ) : ℝ) / |((signUnit x : ℝˣ) : ℝ)| = (x : ℝ) / |(x : ℝ)| := by
  rw [abs_signUnit, div_one, signUnit_val, div_eq_mul_inv, mul_inv_abs_eq_signReal x.ne_zero]

/-- The characters of the positions of real blocks are `χ_l(x) = χ_l(sgn x) |x|^(e_l)`. -/
theorem realPositionCharacter_eq_signUnit_mul : ∀ (ds : List RealBlock) (l : ℕ) (x : ℝˣ),
    realPositionCharacter ds l x =
      realPositionCharacter ds l (signUnit x) *
        ((|(x : ℝ)| : ℝ) : ℂ) ^ realPositionExponent ds l
  | [], _, x => by simp [realPositionCharacter, realPositionExponent]
  | .character d :: _, 0, x => by
      simp only [realPositionCharacter, realPositionExponent]
      rw [d.character_eq, d.character_eq, signUnit_div_abs, abs_signUnit]
      simp
  | .character _ :: ds, p + 1, x => by
      simp only [realPositionCharacter, realPositionExponent]
      exact realPositionCharacter_eq_signUnit_mul ds p x
  | .induced d :: _, 0, x => by
      simp only [realPositionCharacter, realPositionExponent, realInducedFirstCharacter]
      rw [signUnit_div_abs, abs_signUnit]
      simp
  | .induced d :: _, 1, x => by
      simp only [realPositionCharacter, realPositionExponent, realInducedSecondCharacter]
      rw [abs_signUnit]
      simp
  | .induced _ :: ds, p + 2, x => by
      simp only [realPositionCharacter, realPositionExponent]
      exact realPositionCharacter_eq_signUnit_mul ds p x

end GramFormula

open GramFormula

/-- **Statement (Gram formula for `O(n)`-finite principal-series functions).** Let `ds` be a list
of real blocks and `f` an `O(n)`-finite function in the smooth principal series of the position
characters of `ds`. Then there is a polynomial `P` in the `n²` matrix entries such that for
every `x ∈ GL_n(ℝ)`,
`f(x) = ∏ₗ G_l(x)^(s_l/2) G_{l+1}(x)^(-s_l/2) · P(κ̂(x))`,
where `G_l = gram l` is the Gram determinant of the rows `l, …, n-1` of `x`,
`κ̂(x)_ij = gramColumn i j x · G_i(x)^(-1/2) G_{i+1}(x)^(-1/2)`, and `s_l` is the exponent of
`|·|` at position `l` plus `(n-1)/2 - l` (`gramExpression` at the complexified matrix). -/
def PrincipalSeriesGramFormulaStatement : Prop :=
  ∀ (n : ℕ) (ds : List RealBlock) (f : Langlands.GeneralLinear n ℝ → ℂ),
    f ∈ kFiniteFunctions (principalSeries ℝ n (realPositionCharacter ds)) (unitaryCompact ℝ n) →
      ∃ P : MvPolynomial (Fin n × Fin n) ℂ, ∀ x : Langlands.GeneralLinear n ℝ,
        f x = gramExpression (shiftedExponent n (realPositionExponent ds)) P
          (complexify (x : Matrix (Fin n) (Fin n) ℝ))

theorem principalSeriesGramFormula : PrincipalSeriesGramFormulaStatement :=
  fun _ ds _ hf =>
    exists_gramExpression_eq (realPositionExponent ds) (realPositionCharacter_eq_signUnit_mul ds) hf

end Langlands.Archimedean
