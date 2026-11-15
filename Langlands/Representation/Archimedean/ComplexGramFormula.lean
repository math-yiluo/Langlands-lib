import Langlands.Representation.Archimedean.UnitaryFinitePolynomial
import Langlands.Representation.Archimedean.PrincipalSeriesGramFormula
import Langlands.Representation.Archimedean.ComplexDuality.GramWeight

/-!
# `U(n)`-finite complex principal-series functions as polarized Gram expressions

Every `U(n)`-finite function `f` of a principal series of `GL_n(ℂ)` is given on all of `GL_n(ℂ)`
by a closed formula in the entries of `x` and of `conj x`: complex powers of the polarized Gram
determinants `G_l(x, conj x)` of the lower rows times a polynomial in the polarized Iwasawa
coordinates. The formula makes sense for two independent complex matrices `Z, Y`
(`gramExpression`), which gives holomorphic extensions of `t ↦ f(g exp(tH))`.
-/

noncomputable section

open Matrix

open scoped Manifold ContDiff Matrix.Norms.Operator ComplexConjugate

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

namespace ComplexGramFormula

set_option autoImplicit false

-- The charts on units need reduction through the normed-ring instances of matrices.
set_option backward.isDefEq.respectTransparency false

open GramFormula

/-! ## Polarized Gram determinants over a commutative ring -/

section Ring

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The polarized Gram matrix `x yᵀ` on the rows and columns `≥ i`, padded by the identity
matrix on the other rows and columns. -/
def paddedGram (i : ℕ) (x y : Matrix (Fin n) (Fin n) R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun p q =>
    if i ≤ (p : ℕ) ∧ i ≤ (q : ℕ) then (x * yᵀ) p q else (1 : Matrix (Fin n) (Fin n) R) p q

/-- The polarized Gram determinant of the rows `i, …, n-1` of `x` and `y`. -/
def gram (i : ℕ) (x y : Matrix (Fin n) (Fin n) R) : R :=
  (paddedGram i x y).det

/-- The determinant of the polarized padded Gram matrix with its `i`-th column replaced by the
`j`-th column of `x` (on the rows `≥ i`). -/
def gramColumn (i j : Fin n) (x y : Matrix (Fin n) (Fin n) R) : R :=
  ((paddedGram i x y).updateCol i (gramColumnVector i j x)).det

theorem paddedGram_swap (i : ℕ) (x y : Matrix (Fin n) (Fin n) R) :
    paddedGram i y x = (paddedGram i x y)ᵀ := by
  ext p q
  simp only [paddedGram, Matrix.of_apply, Matrix.transpose_apply]
  by_cases h : i ≤ (p : ℕ) ∧ i ≤ (q : ℕ)
  · rw [ite_eq_left h, ite_eq_left ⟨h.2, h.1⟩, ← Matrix.transpose_apply (x * yᵀ),
      Matrix.transpose_mul, Matrix.transpose_transpose]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.2, h'.1⟩), Matrix.one_apply,
      Matrix.one_apply]
    by_cases hpq : p = q
    · subst hpq; rfl
    · rw [ite_eq_right hpq, ite_eq_right (Ne.symm hpq)]

theorem gram_swap (i : ℕ) (x y : Matrix (Fin n) (Fin n) R) : gram i y x = gram i x y := by
  rw [gram, gram, paddedGram_swap, Matrix.det_transpose]

variable {b c κ ν : Matrix (Fin n) (Fin n) R}

theorem mul_mul_transpose (hκ : κ * νᵀ = 1) : (b * κ) * (c * ν)ᵀ = b * cᵀ := by
  rw [Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc κ, hκ, Matrix.one_mul]

theorem paddedGram_mul (hb : b.IsUpperTriangular) (hc : c.IsUpperTriangular)
    (hκ : κ * νᵀ = 1) (i : ℕ) :
    paddedGram i (b * κ) (c * ν) = padded i b * (padded i c)ᵀ := by
  ext p q
  rw [Matrix.mul_apply']
  simp only [paddedGram, Matrix.of_apply, mul_mul_transpose hκ, Matrix.transpose_apply]
  change _ = padded i b p ⬝ᵥ padded i c q
  by_cases hp : i ≤ (p : ℕ)
  · by_cases hq : i ≤ (q : ℕ)
    · rw [ite_eq_left ⟨hp, hq⟩, row_padded_of_le hb hp, row_padded_of_le hc hq, Matrix.mul_apply']
      rfl
    · have hqp : q < p := by rw [Fin.lt_def]; omega
      rw [ite_eq_right (fun h => hq h.2), row_padded_of_le hb hp, row_padded_of_lt c (by omega),
        dotProduct_single, mul_one, hb hqp, Matrix.one_apply_ne (ne_of_gt hqp)]
  · rw [ite_eq_right (fun h => hp h.1), row_padded_of_lt b (by omega), single_dotProduct, one_mul]
    by_cases hq : i ≤ (q : ℕ)
    · have hpq : p < q := by rw [Fin.lt_def]; omega
      rw [row_padded_of_le hc hq, hc hpq, Matrix.one_apply_ne (ne_of_lt hpq)]
    · rw [row_padded_of_lt c (by omega), Pi.single_apply, Matrix.one_apply]

theorem gram_mul (hb : b.IsUpperTriangular) (hc : c.IsUpperTriangular) (hκ : κ * νᵀ = 1)
    (i : ℕ) : gram i (b * κ) (c * ν) = diagonalTail i b * diagonalTail i c := by
  rw [gram, paddedGram_mul hb hc hκ, Matrix.det_mul, Matrix.det_transpose, det_padded hb,
    det_padded hc]

theorem updateCol_paddedGram_mul (hb : b.IsUpperTriangular) (hκ : κ * νᵀ = 1) (i j : Fin n) :
    (paddedGram i (b * κ) (c * ν)).updateCol i (gramColumnVector i j (b * κ)) =
      padded i b * columnFactor i j c κ := by
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

theorem gramColumn_mul (hb : b.IsUpperTriangular) (hc : c.IsUpperTriangular)
    (hκ : κ * νᵀ = 1) (i j : Fin n) :
    gramColumn i j (b * κ) (c * ν) =
      diagonalTail (i : ℕ) b * (κ i j * diagonalTail ((i : ℕ) + 1) c) := by
  rw [gramColumn, updateCol_paddedGram_mul hb hκ, Matrix.det_mul, det_padded hb,
    det_columnFactor hc]

end Ring

/-! ## The polarized Gram expression -/

variable {n : ℕ}

/-- The polarized Iwasawa coordinate `κ̂_ij(Z, Y) = gramColumn i j Z Y · G_i^(-1/2) G_{i+1}^(-1/2)`
with `G_l = gram l Z Y` and principal powers. At `Y = conj Z` with `Z = b κ` (`b` upper
triangular, `κ` unitary) it is `(b_ii/|b_ii|) κ_ij` (`hatCoord_conj`). -/
def hatCoord (i j : Fin n) (Z Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  gramColumn i j Z Y * gram (i : ℕ) Z Y ^ (-(1 / 2 : ℂ)) *
    gram ((i : ℕ) + 1) Z Y ^ (-(1 / 2 : ℂ))

/-- The polarized Gram expression of exponents `s` and a polynomial `P` in `2n²` variables at a
pair of complex matrices `(Z, Y)`:
`∏ₗ G_l^(s_l) G_{l+1}^(-s_l) · P(κ̂(Z, Y), κ̂(Y, Z))`, with `G_l = gram l Z Y`, the variables
`Sum.inl (i, j)` evaluated at `κ̂_ij(Z, Y)` and `Sum.inr (i, j)` at `κ̂_ij(Y, Z)`. -/
def gramExpression (s : Fin n → ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ)
    (Z Y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (∏ l : Fin n, gram (l : ℕ) Z Y ^ s l * gram ((l : ℕ) + 1) Z Y ^ (-s l)) *
    MvPolynomial.eval (Sum.elim (fun ij : Fin n × Fin n => hatCoord ij.1 ij.2 Z Y)
      (fun ij : Fin n × Fin n => hatCoord ij.1 ij.2 Y Z)) P

/-- The phase `z / |z|` of a nonzero complex number, as a unit. -/
def phaseUnit (z : ℂˣ) : ℂˣ :=
  Units.mk0 ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) (div_ne_zero z.ne_zero
    (by exact_mod_cast norm_ne_zero_iff.mpr z.ne_zero))

theorem phaseUnit_val (z : ℂˣ) : ((phaseUnit z : ℂˣ) : ℂ) = (z : ℂ) / (‖(z : ℂ)‖ : ℂ) :=
  rfl

theorem norm_phaseUnit (z : ℂˣ) : ‖((phaseUnit z : ℂˣ) : ℂ)‖ = 1 := by
  rw [phaseUnit_val, norm_div, Complex.norm_real, norm_norm,
    div_self (norm_ne_zero_iff.mpr z.ne_zero)]

theorem conj_mul_self_eq (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem self_mul_conj_eq (z : ℂ) : z * conj z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- `diagonalTail` commutes with entrywise conjugation. -/
theorem diagonalTail_map_conj (i : ℕ) (b : Matrix (Fin n) (Fin n) ℂ) :
    diagonalTail i (b.map (starRingEnd ℂ)) = conj (diagonalTail i b) := by
  rw [diagonalTail, diagonalTail, map_prod]
  refine Finset.prod_congr rfl fun l _ => ?_
  split_ifs <;> simp

theorem isUpperTriangular_map_conj {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular) :
    (b.map (starRingEnd ℂ)).IsUpperTriangular := by
  intro p q hqp
  simp [hb hqp]

theorem diagonalTail_ne_zero' {b : Matrix (Fin n) (Fin n) ℂ} (hd : ∀ l, b l l ≠ 0) (i : ℕ) :
    diagonalTail i b ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun l _ => by
    split_ifs
    exacts [hd l, one_ne_zero]

/-- For `r > 0`, `((r²)^(-1/2)) = r⁻¹` with the principal branch. -/
theorem ofReal_sq_cpow_neg_half {r : ℝ} (hr : 0 < r) :
    ((r ^ 2 : ℝ) : ℂ) ^ (-(1 / 2 : ℂ)) = ((r : ℝ) : ℂ)⁻¹ := by
  rw [show (-(1 / 2 : ℂ)) = (-1) / 2 by ring, ofReal_sq_cpow_half hr.ne', abs_of_pos hr,
    Complex.cpow_neg_one]

/-- For `0 < r` and `0 < q`, `(r²)^s (q²)^(-s) = ((r/q)²)^s`-type cancellation in the form used
below: `((r q)²)^s ((q²)^s)⁻¹ = (r²)^s`. -/
theorem ofReal_sq_mul_cpow_div {r q : ℝ} (hq : 0 < q) (s : ℂ) :
    (((r * q) ^ 2 : ℝ) : ℂ) ^ s * ((q ^ 2 : ℝ) : ℂ) ^ (-s) = ((r ^ 2 : ℝ) : ℂ) ^ s := by
  have hq2 : ((q ^ 2 : ℝ) : ℂ) ^ s ≠ 0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (pow_pos hq 2).ne'))
  rw [mul_pow, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (sq_nonneg r) (sq_nonneg q), Complex.cpow_neg, mul_assoc,
    mul_inv_cancel₀ hq2, mul_one]

/-- The polarized Gram determinants at `(b κ, conj (b κ))`. -/
theorem gram_mul_conj {b κ : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular)
    (hκ : κ * (κ.map (starRingEnd ℂ))ᵀ = 1) (i : ℕ) :
    gram i (b * κ) ((b * κ).map (starRingEnd ℂ)) = ((‖diagonalTail i b‖ ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.map_mul, gram_mul hb (isUpperTriangular_map_conj hb) hκ, diagonalTail_map_conj,
    self_mul_conj_eq]

theorem gram_conj_mul {b κ : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular)
    (hκ : κ * (κ.map (starRingEnd ℂ))ᵀ = 1) (i : ℕ) :
    gram i ((b * κ).map (starRingEnd ℂ)) (b * κ) = ((‖diagonalTail i b‖ ^ 2 : ℝ) : ℂ) := by
  rw [gram_swap, gram_mul_conj hb hκ]

theorem conj_mul_transpose_eq_one {κ : Matrix (Fin n) (Fin n) ℂ}
    (hκ : κ * (κ.map (starRingEnd ℂ))ᵀ = 1) :
    κ.map (starRingEnd ℂ) * κᵀ = 1 := by
  have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M.map (starRingEnd ℂ)) hκ
  simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map] at h
  have hid : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := funext fun z => by simp
  rw [hid, Matrix.map_id, Matrix.map_one _ (map_zero _) (map_one _)] at h
  exact h

/-- The polarized Iwasawa coordinates at `(b κ, conj (b κ))`. -/
theorem hatCoord_mul_conj {b κ : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular)
    (hd : ∀ l, b l l ≠ 0) (hκ : κ * (κ.map (starRingEnd ℂ))ᵀ = 1) (i j : Fin n) :
    hatCoord i j (b * κ) ((b * κ).map (starRingEnd ℂ)) =
      (b i i / (‖b i i‖ : ℂ)) * κ i j := by
  have hT := diagonalTail_ne_zero' hd
  have hpos : ∀ i : ℕ, 0 < ‖diagonalTail i b‖ := fun i => norm_pos_iff.mpr (hT i)
  rw [hatCoord, gram_mul_conj hb hκ, gram_mul_conj hb hκ, ofReal_sq_cpow_neg_half (hpos _),
    ofReal_sq_cpow_neg_half (hpos _), Matrix.map_mul,
    gramColumn_mul hb (isUpperTriangular_map_conj hb) hκ, diagonalTail_map_conj,
    diagonalTail_succ b i, norm_mul, Complex.ofReal_mul]
  have hb0 : (‖b i i‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr (hd i)
  have hT0 : (‖diagonalTail ((i : ℕ) + 1) b‖ : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  have hconj : diagonalTail ((i : ℕ) + 1) b * conj (diagonalTail ((i : ℕ) + 1) b) =
      (‖diagonalTail ((i : ℕ) + 1) b‖ : ℂ) * (‖diagonalTail ((i : ℕ) + 1) b‖ : ℂ) := by
    rw [self_mul_conj_eq, Complex.ofReal_pow, sq]
  field_simp
  linear_combination (b i i * κ i j) * hconj

theorem hatCoord_conj_mul {b κ : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular)
    (hd : ∀ l, b l l ≠ 0) (hκ : κ * (κ.map (starRingEnd ℂ))ᵀ = 1) (i j : Fin n) :
    hatCoord i j ((b * κ).map (starRingEnd ℂ)) (b * κ) =
      conj ((b i i / (‖b i i‖ : ℂ)) * κ i j) := by
  have hd' : ∀ l, (b.map (starRingEnd ℂ)) l l ≠ 0 := fun l => by
    simpa using hd l
  have hκ' := conj_mul_transpose_eq_one hκ
  have h := hatCoord_mul_conj (isUpperTriangular_map_conj hb) hd'
    (κ := κ.map (starRingEnd ℂ)) (by
      rw [Matrix.map_map]
      have hid : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := funext fun z => by simp
      rw [hid, Matrix.map_id]
      exact hκ') i j
  rw [← Matrix.map_mul] at h
  have hmm : ((b * κ).map (starRingEnd ℂ)).map (starRingEnd ℂ) = b * κ := by
    rw [Matrix.map_map]
    have hid : (starRingEnd ℂ) ∘ (starRingEnd ℂ) = id := funext fun z => by simp
    rw [hid, Matrix.map_id]
  rw [hmm] at h
  rw [h]
  simp [map_div₀, Complex.conj_ofReal]


/-! ## `U(n)`-finite principal-series functions -/

theorem principalSeriesCharacter_eq {χ : ℕ → ℂˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (z : ℂˣ), χ l z = χ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l)
    (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n χ a =
      (∏ l : Fin n, ((‖(a l : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ shiftedExponent n e l) *
        principalSeriesCharacter ℂ n χ (fun l => phaseUnit (a l)) := by
  simp only [principalSeriesCharacter, Complex.finrank_real_complex, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun l _ => ?_
  have ha : ((‖(a l : ℂ)‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast pow_ne_zero 2 (norm_ne_zero_iff.mpr (a l).ne_zero)
  rw [hχ l (a l), norm_phaseUnit, one_pow, Complex.ofReal_one, Complex.one_cpow, mul_one,
    shiftedExponent, Complex.cpow_add _ _ ha]
  ring

theorem diagonalUnits_phaseUnit_mem (a : Fin n → ℂˣ) :
    (Iwasawa.diagonalUnits (fun l => phaseUnit (a l)) : Langlands.GeneralLinear n ℂ) ∈
      unitaryCompact ℂ n := by
  change (Matrix.diagonal fun l => ((phaseUnit (a l) : ℂˣ) : ℂ)) ∈ Matrix.unitaryGroup (Fin n) ℂ
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext l
  simp only [Pi.star_apply]
  rw [Complex.star_def, self_mul_conj_eq, norm_phaseUnit]
  simp

theorem isUpperTriangular_diagonal_mul (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) :
    (Matrix.diagonal (fun l => (a l : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)).IsUpperTriangular :=
  (Matrix.blockTriangular_diagonal _).mul u.property.1

theorem diagonal_mul_apply_self (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (l : Fin n) :
    (Matrix.diagonal (fun l => (a l : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) l l = a l := by
  rw [Matrix.diagonal_mul, u.property.2 l, mul_one]

theorem mul_conj_transpose_eq_one_of_mem {k : Langlands.GeneralLinear n ℂ}
    (hk : k ∈ unitaryCompact ℂ n) :
    (k : Matrix (Fin n) (Fin n) ℂ) * ((k : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))ᵀ = 1 := by
  have h := Matrix.mem_unitaryGroup_iff.mp hk
  rw [Matrix.star_eq_conjTranspose] at h
  convert h using 2
  ext i j
  simp [Matrix.conjTranspose_apply]

/-- The Gram expression at `(b κ, conj (b κ))`, with `b` upper triangular with nonzero diagonal
and `κ` unitary. -/
theorem gramExpression_mul_conj {b κ : Matrix (Fin n) (Fin n) ℂ}
    (hb : b.IsUpperTriangular) (hd : ∀ l, b l l ≠ 0) (hκ : κ * (κ.map (starRingEnd ℂ))ᵀ = 1)
    (s : Fin n → ℂ) (P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ) :
    gramExpression s P (b * κ) ((b * κ).map (starRingEnd ℂ)) =
      (∏ l : Fin n, ((‖b l l‖ ^ 2 : ℝ) : ℂ) ^ s l) *
        MvPolynomial.eval (Sum.elim
          (fun ij : Fin n × Fin n => (b ij.1 ij.1 / (‖b ij.1 ij.1‖ : ℂ)) * κ ij.1 ij.2)
          (fun ij : Fin n × Fin n => conj ((b ij.1 ij.1 / (‖b ij.1 ij.1‖ : ℂ)) * κ ij.1 ij.2)))
          P := by
  have hT := diagonalTail_ne_zero' hd
  have hpos : ∀ i : ℕ, 0 < ‖diagonalTail i b‖ := fun i => norm_pos_iff.mpr (hT i)
  unfold gramExpression
  congr 1
  · refine Finset.prod_congr rfl fun l _ => ?_
    rw [gram_mul_conj hb hκ, gram_mul_conj hb hκ, diagonalTail_succ b l, norm_mul,
      ofReal_sq_mul_cpow_div (hpos _)]
  · refine congrArg (fun v => MvPolynomial.eval v P) (funext fun v => ?_)
    cases v with
    | inl ij => exact hatCoord_mul_conj hb hd hκ ij.1 ij.2
    | inr ij => exact hatCoord_conj_mul hb hd hκ ij.1 ij.2

/-- **Gram formula.** Let the characters satisfy `χ_l(z) = χ_l(z/|z|) (|z|²)^(e_l)`. Every
`U(n)`-finite function `f` of the principal series of `χ` is a polarized Gram expression: there
is a polynomial `P` in `2n²` variables with
`f(x) = gramExpression (shiftedExponent n e) P x (conj x)` for every `x ∈ GL_n(ℂ)`. -/
theorem exists_gramExpression_eq {χ : ℕ → ℂˣ → ℂ} (e : ℕ → ℂ)
    (hχ : ∀ (l : ℕ) (z : ℂˣ), χ l z = χ l (phaseUnit z) * ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ e l)
    {f : Langlands.GeneralLinear n ℂ → ℂ}
    (hf : f ∈ kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n)) :
    ∃ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ,
      ∀ x : Langlands.GeneralLinear n ℂ,
        f x = gramExpression (shiftedExponent n e) P (x : Matrix (Fin n) (Fin n) ℂ)
          ((x : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ)) := by
  obtain ⟨hps, hK⟩ := Submodule.mem_inf.mp hf
  obtain ⟨P, hP⟩ := UnitaryFinitePolynomial.exists_mvPolynomial_of_mem_kFiniteVectors
    hps.1.continuous hK 1
  refine ⟨P, fun x => ?_⟩
  obtain ⟨a, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary x
  let b : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal (fun l => (a l : ℂ)) *
    ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have hb : b.IsUpperTriangular := isUpperTriangular_diagonal_mul a u
  have hbd : ∀ l, b l l = a l := diagonal_mul_apply_self a u
  have hd : ∀ l, b l l ≠ 0 := fun l => by rw [hbd]; exact (a l).ne_zero
  have hκ := mul_conj_transpose_eq_one_of_mem hk
  have hx : (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
      (u : Langlands.GeneralLinear n ℂ) * k : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) = b * (k : Matrix (Fin n) (Fin n) ℂ) := rfl
  rw [hx, gramExpression_mul_conj hb hd hκ, hps.2 a u k]
  -- the polynomial at the phase-twisted unitary matrix
  let y : Langlands.GeneralLinear n ℂ :=
    (Iwasawa.diagonalUnits (fun l => phaseUnit (a l)) : Langlands.GeneralLinear n ℂ) * k
  have hy : y ∈ unitaryCompact ℂ n := mul_mem (diagonalUnits_phaseUnit_mem a) hk
  have hPy := hP ⟨(y : Matrix (Fin n) (Fin n) ℂ), hy⟩
  have hyu : Unitary.toUnits (⟨(y : Matrix (Fin n) (Fin n) ℂ), hy⟩ :
      Matrix.unitaryGroup (Fin n) ℂ) = y := Units.ext rfl
  rw [one_mul, hyu] at hPy
  have hfy : f y = principalSeriesCharacter ℂ n χ (fun l => phaseUnit (a l)) * f k := by
    have := hps.2 (fun l => phaseUnit (a l)) 1 k
    rwa [OneMemClass.coe_one, mul_one] at this
  have hentry : ∀ ij : Fin n × Fin n, (b ij.1 ij.1 / (‖b ij.1 ij.1‖ : ℂ)) *
      (k : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2 = (y : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2 := by
    intro ij
    change _ = ((Matrix.diagonal fun l => ((phaseUnit (a l) : ℂˣ) : ℂ)) *
      (k : Matrix (Fin n) (Fin n) ℂ)) ij.1 ij.2
    rw [Matrix.diagonal_mul, phaseUnit_val, hbd]
  have hentries : (Sum.elim (fun ij : Fin n × Fin n => (b ij.1 ij.1 / (‖b ij.1 ij.1‖ : ℂ)) *
      (k : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2)
      (fun ij : Fin n × Fin n => conj ((b ij.1 ij.1 / (‖b ij.1 ij.1‖ : ℂ)) *
        (k : Matrix (Fin n) (Fin n) ℂ) ij.1 ij.2))) =
        UnitaryFinitePolynomial.coordValue
          (⟨(y : Matrix (Fin n) (Fin n) ℂ), hy⟩ : Matrix.unitaryGroup (Fin n) ℂ) := by
    funext v
    cases v with
    | inl ij => exact hentry ij
    | inr ij =>
      change conj _ = star _
      rw [hentry ij]
      rfl
  have hprod : (∏ l : Fin n, ((‖b l l‖ ^ 2 : ℝ) : ℂ) ^ shiftedExponent n e l) =
      ∏ l : Fin n, ((‖(a l : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ shiftedExponent n e l :=
    Finset.prod_congr rfl fun l _ => by rw [hbd]
  rw [hentries, ← hPy, hfy, hprod, principalSeriesCharacter_eq e hχ a]
  ring

/-- For `r > 0`, `r^(2t) = (r²)^t` with principal powers. -/
theorem ofReal_cpow_two_mul {r : ℝ} (hr : 0 < r) (t : ℂ) :
    ((r : ℝ) : ℂ) ^ (2 * t) = ((r ^ 2 : ℝ) : ℂ) ^ t := by
  have h1 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have h2 : ((r ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (pow_pos hr 2).ne'
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2,
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log (pow_pos hr 2).le, Real.log_pow]
  push_cast
  ring_nf

/-! ## Standard modules -/

/-- The exponent `t` of `|z|²` in the character at each diagonal position of a list of complex
characters; `0` past the end. -/
def complexPositionExponent : List ComplexCharacterData → ℕ → ℂ
  | [], _ => 0
  | d :: _, 0 => d.exponent
  | _ :: ds, p + 1 => complexPositionExponent ds p

/-- The position characters of a list of complex characters satisfy
`χ_l(z) = χ_l(z/|z|) (|z|²)^(t_l)`. -/
theorem complexPositionCharacter_eq_phaseUnit_mul : ∀ (ds : List ComplexCharacterData) (l : ℕ)
    (z : ℂˣ), complexPositionCharacter ds l z =
      complexPositionCharacter ds l (phaseUnit z) *
        ((‖(z : ℂ)‖ ^ 2 : ℝ) : ℂ) ^ complexPositionExponent ds l
  | [], _, z => by simp [complexPositionCharacter, complexPositionExponent]
  | d :: _, 0, z => by
      simp only [complexPositionCharacter, complexPositionExponent]
      rw [d.character_eq, d.character_eq, norm_phaseUnit, Complex.ofReal_one, div_one,
        Complex.one_cpow, mul_one, phaseUnit_val,
        ofReal_cpow_two_mul (norm_pos_iff.mpr z.ne_zero)]
  | _ :: ds, p + 1, z => by
      simp only [complexPositionCharacter, complexPositionExponent]
      exact complexPositionCharacter_eq_phaseUnit_mul ds p z

end ComplexGramFormula

open ComplexGramFormula

/-- **Statement (Gram formula for `U(n)`-finite complex principal-series functions).** Let `ds` be
a list of complex characters and `f` a `U(n)`-finite function in the smooth principal series of
the position characters of `ds`. Then there is a polynomial `P` in `2n²` variables such that for
every `x ∈ GL_n(ℂ)`,
`f(x) = ∏ₗ G_l(x, x̄)^(s_l) G_{l+1}(x, x̄)^(-s_l) · P(κ̂(x, x̄), κ̂(x̄, x))`,
where `x̄` is the entrywise complex conjugate, `G_l = gram l` is the polarized Gram determinant
of the rows `l, …, n-1`, `κ̂(Z, Y)_ij = gramColumn i j Z Y · G_i^(-1/2) G_{i+1}^(-1/2)`, and
`s_l = t_l + (n-1)/2 - l` with `t_l` the exponent at position `l` (`gramExpression`). -/
def ComplexPrincipalSeriesGramFormulaStatement : Prop :=
  ∀ (n : ℕ) (ds : List ComplexCharacterData) (f : Langlands.GeneralLinear n ℂ → ℂ),
    f ∈ kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n) →
      ∃ P : MvPolynomial ((Fin n × Fin n) ⊕ (Fin n × Fin n)) ℂ,
        ∀ x : Langlands.GeneralLinear n ℂ,
          f x = gramExpression (GramFormula.shiftedExponent n (complexPositionExponent ds)) P
            (x : Matrix (Fin n) (Fin n) ℂ) ((x : Matrix (Fin n) (Fin n) ℂ).map (starRingEnd ℂ))

theorem complexPrincipalSeriesGramFormula : ComplexPrincipalSeriesGramFormulaStatement :=
  fun _ ds _ hf =>
    exists_gramExpression_eq (complexPositionExponent ds)
      (complexPositionCharacter_eq_phaseUnit_mul ds) hf

end Langlands.Archimedean
