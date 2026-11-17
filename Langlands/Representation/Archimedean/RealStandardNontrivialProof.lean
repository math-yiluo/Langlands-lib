import Langlands.Representation.Archimedean.RealStandardBlockPolynomial
import Langlands.Analysis.InversePowerFourier

/-!
# Real standard modules are nonzero

For a list `ds` of real blocks of total rank `n`, the Gram function of the block polynomial
`blockPoly n ds 0` is a nonzero `O(n)`-finite function of the real standard module
`realStandardModule n ds`.
-/

noncomputable section

open Matrix

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean GramFormula RealGramFunction
  RealBlockRotation

namespace RealStandardNontrivial

set_option autoImplicit false

variable {n p : ℕ}

/-! ## Rotations of two rows and of two columns -/

theorem rotMatrix_eq (h : p + 1 < n) (θ : ℝ) :
    rotMatrix h θ = 1 + (Real.cos θ - 1) • (single (ia h) (ia h) 1 + single (ib h) (ib h) 1) +
      Real.sin θ • (single (ib h) (ia h) 1 - single (ia h) (ib h) 1) := by
  rw [rotMatrix, blockProj, rotationGenerator_eq h]

/-- Left multiplication by `r(θ)` rotates the rows `p, p + 1`. -/
theorem rotMatrix_mul_apply (h : p + 1 < n) (θ : ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (rotMatrix h θ * M) i j =
      if i = ia h then Real.cos θ * M (ia h) j - Real.sin θ * M (ib h) j
      else if i = ib h then Real.sin θ * M (ia h) j + Real.cos θ * M (ib h) j
      else M i j := by
  have hne := ia_ne_ib h
  rw [rotMatrix_eq h]
  simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.add_apply,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  split_ifs with h1 h2
  · subst h1
    simp [hne]
    ring
  · subst h2
    simp [hne.symm]
    ring
  · simp [h1, h2]

/-- Right multiplication by `r(φ)ᵀ` rotates the columns `p, p + 1`. -/
theorem mul_rotMatrix_transpose_apply (h : p + 1 < n) (φ : ℝ) (M : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) :
    (M * (rotMatrix h φ)ᵀ) i j =
      if j = ia h then Real.cos φ * M i (ia h) - Real.sin φ * M i (ib h)
      else if j = ib h then Real.sin φ * M i (ia h) + Real.cos φ * M i (ib h)
      else M i j := by
  rw [show M * (rotMatrix h φ)ᵀ = (rotMatrix h φ * Mᵀ)ᵀ by
    rw [Matrix.transpose_mul, Matrix.transpose_transpose]]
  rw [Matrix.transpose_apply, rotMatrix_mul_apply]
  rfl

theorem rotMatrix_mul_transpose_self (h : p + 1 < n) (φ : ℝ) :
    rotMatrix h φ * (rotMatrix h φ)ᵀ = 1 := by
  have := mul_transpose_eq_one_of_mem (blockRotation_mem_unitaryCompact n p φ)
  rwa [blockRotation_val_eq h] at this

theorem rotMatrix_transpose_mul_self (h : p + 1 < n) (φ : ℝ) :
    (rotMatrix h φ)ᵀ * rotMatrix h φ = 1 :=
  mul_eq_one_comm.mp (rotMatrix_mul_transpose_self h φ)

theorem rotMatrix_mem_unitaryGroup (h : p + 1 < n) (φ : ℝ) :
    rotMatrix h φ ∈ Matrix.unitaryGroup (Fin n) ℝ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  exact rotMatrix_mul_transpose_self h φ

theorem ia_lt_ib (h : p + 1 < n) : ia h < ib h := by
  rw [Fin.lt_def]
  simp [ia, ib]

theorem val_ia (h : p + 1 < n) : ((ia h : Fin n) : ℕ) = p := rfl

theorem val_ib (h : p + 1 < n) : ((ib h : Fin n) : ℕ) = p + 1 := rfl

/-! ## The Iwasawa decomposition of a rotated upper triangular matrix -/

/-- Polar coordinates of a nonzero real vector `(x, y)`. -/
theorem exists_polar {x y : ℝ} (hxy : x ≠ 0 ∨ y ≠ 0) :
    ∃ φ ρ : ℝ, 0 < ρ ∧ ρ ^ 2 = x ^ 2 + y ^ 2 ∧ Real.cos φ * ρ = x ∧ Real.sin φ * ρ = y := by
  set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I with hz
  have hz0 : z ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    have him := congrArg Complex.im h0
    simp [hz] at hre him
    rcases hxy with h | h <;> contradiction
  have hρ : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  refine ⟨Complex.arg z, ‖z‖, hρ, ?_, ?_, ?_⟩
  · rw [Complex.sq_norm, hz, Complex.normSq_add_mul_I]
  · rw [Complex.cos_arg hz0, div_mul_cancel₀ _ hρ.ne']
    simp [hz]
  · rw [Complex.sin_arg, div_mul_cancel₀ _ hρ.ne']
    simp [hz]

variable (h : p + 1 < n) {b : Matrix (Fin n) (Fin n) ℝ}

/-- Rotating the rows `p, p + 1` of an upper triangular matrix keeps the entries below the
diagonal zero, except at `(p + 1, p)`. -/
theorem rotMatrix_mul_apply_eq_zero (hb : b.IsUpperTriangular) (θ : ℝ) {i j : Fin n}
    (hji : j < i) (hij : ¬ ((i : ℕ) = p + 1 ∧ (j : ℕ) = p)) : (rotMatrix h θ * b) i j = 0 := by
  rw [rotMatrix_mul_apply]
  split_ifs with h1 h2
  · subst h1
    have e1 : b (ia h) j = 0 := hb hji
    have e2 : b (ib h) j = 0 := hb (lt_trans hji (ia_lt_ib h))
    rw [e1, e2]
    ring
  · subst h2
    have hj : j < ia h := by
      rw [Fin.lt_def] at hji ⊢
      rw [val_ib] at hji hij
      rw [val_ia]
      omega
    have e1 : b (ia h) j = 0 := hb hj
    have e2 : b (ib h) j = 0 := hb hji
    rw [e1, e2]
    ring
  · exact hb hji


theorem ne_ia_iff {i : Fin n} : i ≠ ia h ↔ (i : ℕ) ≠ p := by
  rw [Ne, Fin.ext_iff, val_ia]

theorem ne_ib_iff {i : Fin n} : i ≠ ib h ↔ (i : ℕ) ≠ p + 1 := by
  rw [Ne, Fin.ext_iff, val_ib]

/-- The entry `c' = sin θ · b_{pp}` at `(p + 1, p)` of `r(θ) b`. -/
def bottomLeft (b : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) : ℝ := Real.sin θ * b (ia h) (ia h)

/-- The entry `d' = sin θ · b_{p,p+1} + cos θ · b_{p+1,p+1}` at `(p + 1, p + 1)` of `r(θ) b`. -/
def bottomRight (b : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) : ℝ :=
  Real.sin θ * b (ia h) (ib h) + Real.cos θ * b (ib h) (ib h)

/-- The matrix `r(θ) b r(φ)ᵀ`. -/
def rotated (b : Matrix (Fin n) (Fin n) ℝ) (θ φ : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  rotMatrix h θ * b * (rotMatrix h φ)ᵀ

theorem bottom_ne_zero (hd : ∀ l, b l l ≠ 0) (θ : ℝ) :
    bottomRight h b θ ≠ 0 ∨ bottomLeft h b θ ≠ 0 := by
  by_cases hs : Real.sin θ = 0
  · left
    have hc : Real.cos θ ≠ 0 := by
      intro hc
      have := Real.sin_sq_add_cos_sq θ
      rw [hs, hc] at this
      norm_num at this
    rw [bottomRight, hs, zero_mul, zero_add]
    exact mul_ne_zero hc (hd _)
  · right
    exact mul_ne_zero hs (hd _)

theorem rotMatrix_mul_apply_of_ne {θ : ℝ} {M : Matrix (Fin n) (Fin n) ℝ} {i : Fin n}
    (hi1 : i ≠ ia h) (hi2 : i ≠ ib h) (j : Fin n) : (rotMatrix h θ * M) i j = M i j := by
  rw [rotMatrix_mul_apply]
  simp [hi1, hi2]

section Rotated

variable {θ φ ρ : ℝ}

theorem rotated_apply_of_ne {i j : Fin n} (hj1 : j ≠ ia h) (hj2 : j ≠ ib h) :
    rotated h b θ φ i j = (rotMatrix h θ * b) i j := by
  rw [rotated, mul_rotMatrix_transpose_apply]
  simp [hj1, hj2]

theorem rotated_isUpperTriangular (hb : b.IsUpperTriangular) (hρ : 0 < ρ)
    (hu : Real.cos φ * ρ = bottomRight h b θ) (hv : Real.sin φ * ρ = bottomLeft h b θ) :
    (rotated h b θ φ).IsUpperTriangular := by
  intro i j hji
  have hji' : (j : ℕ) < i := hji
  have hne := ia_ne_ib h
  have hA : b (ib h) (ia h) = 0 := hb (ia_lt_ib h)
  have hz : ∀ i j : Fin n, (j : ℕ) < i → b i j = 0 := fun i j hij => hb hij
  by_cases hja : j = ia h
  · subst hja
    rw [rotated, mul_rotMatrix_transpose_apply]
    simp only [ite_true]
    by_cases hib : i = ib h
    · subst hib
      rw [rotMatrix_mul_apply, rotMatrix_mul_apply]
      simp only [hne.symm, ite_false, ite_true]
      rw [hA]
      have key : (Real.cos φ * (Real.sin θ * b (ia h) (ia h) + Real.cos θ * 0) -
          Real.sin φ * (Real.sin θ * b (ia h) (ib h) + Real.cos θ * b (ib h) (ib h))) * ρ = 0 := by
        rw [bottomRight] at hu
        rw [bottomLeft] at hv
        linear_combination (Real.sin θ * b (ia h) (ia h)) * hu -
          (Real.sin θ * b (ia h) (ib h) + Real.cos θ * b (ib h) (ib h)) * hv
      rcases mul_eq_zero.mp key with h0 | h0
      · exact h0
      · exact absurd h0 hρ.ne'
    · have hia : i ≠ ia h := fun e => by
        rw [e] at hji'
        exact lt_irrefl _ hji'
      rw [rotMatrix_mul_apply_of_ne h hia hib, rotMatrix_mul_apply_of_ne h hia hib]
      have h1 := (ne_ib_iff h).mp hib
      rw [val_ia] at hji'
      rw [hz _ _ (by rw [val_ia]; omega), hz _ _ (by rw [val_ib]; omega)]
      ring
  · by_cases hjb : j = ib h
    · subst hjb
      have hia : i ≠ ia h := fun e => by
        rw [e, val_ia, val_ib] at hji'
        omega
      have hib : i ≠ ib h := fun e => by
        rw [e] at hji'
        exact lt_irrefl _ hji'
      rw [rotated, mul_rotMatrix_transpose_apply]
      simp only [hne.symm, ite_false, ite_true]
      rw [rotMatrix_mul_apply_of_ne h hia hib, rotMatrix_mul_apply_of_ne h hia hib]
      rw [val_ib] at hji'
      rw [hz _ _ (by rw [val_ia]; omega), hz _ _ (by rw [val_ib]; omega)]
      ring
    · rw [rotated_apply_of_ne h hja hjb, rotMatrix_mul_apply]
      have hja' := (ne_ia_iff h).mp hja
      split_ifs with h1 h2
      · subst h1
        rw [val_ia] at hji'
        rw [hz _ _ (by rw [val_ia]; omega), hz _ _ (by rw [val_ib]; omega)]
        ring
      · subst h2
        rw [val_ib] at hji'
        rw [hz _ _ (by rw [val_ia]; omega), hz _ _ (by rw [val_ib]; omega)]
        ring
      · exact hz _ _ hji'

theorem rotated_apply_self_of_ne {l : Fin n} (hl1 : l ≠ ia h) (hl2 : l ≠ ib h) :
    rotated h b θ φ l l = b l l := by
  rw [rotated_apply_of_ne h hl1 hl2, rotMatrix_mul_apply_of_ne h hl1 hl2]

theorem rotated_ia_mul (hb : b.IsUpperTriangular)
    (hu : Real.cos φ * ρ = bottomRight h b θ) (hv : Real.sin φ * ρ = bottomLeft h b θ) :
    rotated h b θ φ (ia h) (ia h) * ρ = b (ia h) (ia h) * b (ib h) (ib h) := by
  have hne := ia_ne_ib h
  have hA : b (ib h) (ia h) = 0 := hb (ia_lt_ib h)
  rw [rotated, mul_rotMatrix_transpose_apply, rotMatrix_mul_apply, rotMatrix_mul_apply]
  simp only [hne, ite_false, ite_true]
  rw [hA]
  rw [bottomRight] at hu
  rw [bottomLeft] at hv
  linear_combination (Real.cos θ * b (ia h) (ia h)) * hu -
    (Real.cos θ * b (ia h) (ib h) - Real.sin θ * b (ib h) (ib h)) * hv +
    b (ia h) (ia h) * b (ib h) (ib h) * Real.sin_sq_add_cos_sq θ

theorem rotated_ib (hb : b.IsUpperTriangular) (hρ : 0 < ρ)
    (hρ2 : ρ ^ 2 = bottomRight h b θ ^ 2 + bottomLeft h b θ ^ 2)
    (hu : Real.cos φ * ρ = bottomRight h b θ) (hv : Real.sin φ * ρ = bottomLeft h b θ) :
    rotated h b θ φ (ib h) (ib h) = ρ := by
  have hne := ia_ne_ib h
  have hA : b (ib h) (ia h) = 0 := hb (ia_lt_ib h)
  refine mul_right_cancel₀ hρ.ne' ?_
  rw [rotated, mul_rotMatrix_transpose_apply, rotMatrix_mul_apply, rotMatrix_mul_apply]
  simp only [hne.symm, ite_false, ite_true]
  rw [hA]
  rw [bottomRight] at hu hρ2
  rw [bottomLeft] at hv hρ2
  linear_combination (Real.sin θ * b (ia h) (ia h)) * hv +
    (Real.sin θ * b (ia h) (ib h) + Real.cos θ * b (ib h) (ib h)) * hu - hρ2

theorem rotated_ia_eq (hb : b.IsUpperTriangular) (hρ : 0 < ρ)
    (hu : Real.cos φ * ρ = bottomRight h b θ) (hv : Real.sin φ * ρ = bottomLeft h b θ) :
    rotated h b θ φ (ia h) (ia h) = b (ia h) (ia h) * b (ib h) (ib h) * ρ⁻¹ := by
  rw [← rotated_ia_mul h hb hu hv, mul_inv_cancel_right₀ hρ.ne']

theorem rotated_diag_ne_zero (hb : b.IsUpperTriangular) (hd : ∀ l, b l l ≠ 0) (hρ : 0 < ρ)
    (hρ2 : ρ ^ 2 = bottomRight h b θ ^ 2 + bottomLeft h b θ ^ 2)
    (hu : Real.cos φ * ρ = bottomRight h b θ) (hv : Real.sin φ * ρ = bottomLeft h b θ) (l : Fin n) :
    rotated h b θ φ l l ≠ 0 := by
  by_cases h1 : l = ia h
  · subst h1
    rw [rotated_ia_eq h hb hρ hu hv]
    exact mul_ne_zero (mul_ne_zero (hd _) (hd _)) (inv_ne_zero hρ.ne')
  · by_cases h2 : l = ib h
    · subst h2
      rw [rotated_ib h hb hρ hρ2 hu hv]
      exact hρ.ne'
    · rw [rotated_apply_self_of_ne h h1 h2]
      exact hd l

/-- `r(θ) b κ = (r(θ) b r(φ)ᵀ) (r(φ) κ)`. -/
theorem rotMatrix_mul_eq (κ : Matrix (Fin n) (Fin n) ℝ) :
    rotMatrix h θ * (b * κ) = rotated h b θ φ * (rotMatrix h φ * κ) := by
  rw [rotated, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (rotMatrix h φ)ᵀ,
    rotMatrix_transpose_mul_self, Matrix.one_mul]

end Rotated

/-! ## The Gram function along the rotations -/

/-- The sign `σ = sgn(b_{pp}) sgn(b_{p+1,p+1})`. -/
def blockSign (b : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  signReal (b (ia h) (ia h)) * signReal (b (ib h) (ib h))

/-- The entries independent of the angle: row `l` off the block is `sgn(b_{ll}) κ_l`, row `p` is
`σ κ_p` and row `p + 1` is `κ_{p+1}`. -/
def baseEntries (b κ : Matrix (Fin n) (Fin n) ℝ) : Fin n × Fin n → ℂ := fun ij =>
  ((if ij.1 = ia h then blockSign h b * κ ij.1 ij.2
    else if ij.1 = ib h then κ ij.1 ij.2 else signReal (b ij.1 ij.1) * κ ij.1 ij.2 : ℝ) : ℂ)

/-- The weights independent of the angle: `|b_{ll}|` off the block, `|b_{pp} b_{p+1,p+1}|` at `p`
and `1` at `p + 1`. -/
def baseWeight (b : Matrix (Fin n) (Fin n) ℝ) (l : Fin n) : ℝ :=
  if l = ia h then |b (ia h) (ia h) * b (ib h) (ib h)| else if l = ib h then 1 else |b l l|

theorem signReal_of_pos {x : ℝ} (hx : 0 < x) : signReal x = 1 := by
  simp [signReal, hx]

theorem blockSign_sq : blockSign h b ^ 2 = 1 := by
  rw [blockSign, mul_pow]
  rcases signReal_eq_one_or (b (ia h) (ia h)) with h1 | h1 <;>
    rcases signReal_eq_one_or (b (ib h) (ib h)) with h2 | h2 <;> rw [h1, h2] <;> norm_num

/-- `(1/ρ^N) (u - i v)^N = (d + i c)^(-N)` when `u ρ = d`, `v ρ = c` and `u² + v² = 1`. -/
theorem inv_pow_mul_sub_eq {ρ u v d c : ℝ} (hρ : ρ ≠ 0) (huv : u ^ 2 + v ^ 2 = 1)
    (hd : u * ρ = d) (hc : v * ρ = c) (N : ℕ) :
    ((ρ : ℂ) ^ N)⁻¹ * ((u : ℂ) - Complex.I * v) ^ N = (((d : ℂ) + Complex.I * c) ^ N)⁻¹ := by
  have hρC : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ
  have huvC : (u : ℂ) ^ 2 + (v : ℂ) ^ 2 = 1 := by exact_mod_cast huv
  have h1 : ((d : ℂ) + Complex.I * c) * ((u : ℂ) - Complex.I * v) = ρ := by
    rw [← hd, ← hc]
    push_cast
    linear_combination (ρ : ℂ) * huvC - (v : ℂ) ^ 2 * ρ * Complex.I_sq
  refine eq_inv_of_mul_eq_one_right ?_
  calc ((d : ℂ) + Complex.I * c) ^ N * (((ρ : ℂ) ^ N)⁻¹ * ((u : ℂ) - Complex.I * v) ^ N)
      = (((d : ℂ) + Complex.I * c) * ((u : ℂ) - Complex.I * v)) ^ N * ((ρ : ℂ) ^ N)⁻¹ := by
        rw [mul_pow]; ring
    _ = 1 := by rw [h1, mul_inv_cancel₀ (pow_ne_zero _ hρC)]

/-- `(1/ρ^N) (u + i v)^N = (d - i c)^(-N)` when `u ρ = d`, `v ρ = c` and `u² + v² = 1`. -/
theorem inv_pow_mul_add_eq {ρ u v d c : ℝ} (hρ : ρ ≠ 0) (huv : u ^ 2 + v ^ 2 = 1)
    (hd : u * ρ = d) (hc : v * ρ = c) (N : ℕ) :
    ((ρ : ℂ) ^ N)⁻¹ * ((u : ℂ) + Complex.I * v) ^ N = (((d : ℂ) - Complex.I * c) ^ N)⁻¹ := by
  have hρC : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ
  have huvC : (u : ℂ) ^ 2 + (v : ℂ) ^ 2 = 1 := by exact_mod_cast huv
  have h1 : ((d : ℂ) - Complex.I * c) * ((u : ℂ) + Complex.I * v) = ρ := by
    rw [← hd, ← hc]
    push_cast
    linear_combination (ρ : ℂ) * huvC - (v : ℂ) ^ 2 * ρ * Complex.I_sq
  refine eq_inv_of_mul_eq_one_right ?_
  calc ((d : ℂ) - Complex.I * c) ^ N * (((ρ : ℂ) ^ N)⁻¹ * ((u : ℂ) + Complex.I * v) ^ N)
      = (((d : ℂ) - Complex.I * c) * ((u : ℂ) + Complex.I * v)) ^ N * ((ρ : ℂ) ^ N)⁻¹ := by
        rw [mul_pow]; ring
    _ = 1 := by rw [h1, mul_inv_cancel₀ (pow_ne_zero _ hρC)]

section Value

variable {θ φ ρ : ℝ}

theorem isRowRotation_rotated (hb : b.IsUpperTriangular) (hd : ∀ l, b l l ≠ 0) (hρ : 0 < ρ)
    (hρ2 : ρ ^ 2 = bottomRight h b θ ^ 2 + bottomLeft h b θ ^ 2)
    (hu : Real.cos φ * ρ = bottomRight h b θ) (hv : Real.sin φ * ρ = bottomLeft h b θ)
    (κ : Matrix (Fin n) (Fin n) ℝ) :
    IsRowRotation h (Real.cos φ : ℂ) ((blockSign h b * Real.sin φ : ℝ) : ℂ)
      (baseEntries h b κ)
      (fun ij => ((signReal (rotated h b θ φ ij.1 ij.1) * (rotMatrix h φ * κ) ij.1 ij.2 : ℝ) : ℂ)) := by
  have hne := ia_ne_ib h
  have hsa : signReal (rotated h b θ φ (ia h) (ia h)) = blockSign h b := by
    rw [rotated_ia_eq h hb hρ hu hv,
      PrincipalSeriesExtension.signReal_mul (mul_ne_zero (hd _) (hd _)) (inv_ne_zero hρ.ne'),
      PrincipalSeriesExtension.signReal_mul (hd _) (hd _), signReal_of_pos (inv_pos.mpr hρ),
      mul_one, blockSign]
  have hsb : signReal (rotated h b θ φ (ib h) (ib h)) = 1 := by
    rw [rotated_ib h hb hρ hρ2 hu hv, signReal_of_pos hρ]
  have hσC : ((blockSign h b : ℝ) : ℂ) ^ 2 = 1 := by exact_mod_cast blockSign_sq h (b := b)
  refine ⟨fun i j hi1 hi2 => ?_, fun j => ?_, fun j => ?_⟩
  · simp only [baseEntries, hi1, hi2, ite_false]
    rw [rotated_apply_self_of_ne h hi1 hi2, rotMatrix_mul_apply_of_ne h hi1 hi2]
  · simp only [baseEntries, hne.symm, ite_false, ite_true]
    rw [hsa, rotMatrix_mul_apply]
    simp only [ite_true]
    push_cast
    ring
  · simp only [baseEntries, hne.symm, ite_false, ite_true]
    rw [hsb, rotMatrix_mul_apply]
    simp only [hne.symm, ite_false, ite_true]
    push_cast
    linear_combination (-(Complex.sin (φ : ℂ) * (κ (ia h) j : ℂ))) * hσC

theorem gramFunction_blockRotation_mul (s : Fin n → ℂ) (P : MvPolynomial (Fin n × Fin n) ℂ)
    (hb : b.IsUpperTriangular) (hd : ∀ l, b l l ≠ 0) {κ : Matrix (Fin n) (Fin n) ℝ}
    (hκ : κ ∈ Matrix.unitaryGroup (Fin n) ℝ) {g : Langlands.GeneralLinear n ℝ}
    (hg : (g : Matrix (Fin n) (Fin n) ℝ) = b * κ) (hρ : 0 < ρ)
    (hρ2 : ρ ^ 2 = bottomRight h b θ ^ 2 + bottomLeft h b θ ^ 2)
    (hu : Real.cos φ * ρ = bottomRight h b θ) (hv : Real.sin φ * ρ = bottomLeft h b θ) :
    gramFunction s P (blockRotation n p θ * g) =
      (∏ l : Fin n, ((|rotated h b θ φ l l| : ℝ) : ℂ) ^ s l) *
        MvPolynomial.eval (fun ij => ((signReal (rotated h b θ φ ij.1 ij.1) *
          (rotMatrix h φ * κ) ij.1 ij.2 : ℝ) : ℂ)) P := by
  have hκ' : rotMatrix h φ * κ ∈ Matrix.unitaryGroup (Fin n) ℝ :=
    Submonoid.mul_mem _ (rotMatrix_mem_unitaryGroup h φ) hκ
  have hx : ((blockRotation n p θ * g : Langlands.GeneralLinear n ℝ) :
      Matrix (Fin n) (Fin n) ℝ) = rotated h b θ φ * (rotMatrix h φ * κ) := by
    rw [Units.val_mul, blockRotation_val_eq h, hg, rotMatrix_mul_eq h (φ := φ)]
  rw [gramFunction_eq_extension, PrincipalSeriesExtension.extension_eq s _
    (rotated_isUpperTriangular h hb hρ hu hv) (rotated_diag_ne_zero h hb hd hρ hρ2 hu hv) hκ' hx]
  congr 1
  unfold orthogonalEval
  refine congrArg (fun v => MvPolynomial.eval v P) (funext fun ij => ?_)
  change ((((Matrix.diagonal fun i => signReal (rotated h b θ φ i i)) *
    (rotMatrix h φ * κ)) ij.1 ij.2 : ℝ) : ℂ) = _
  rw [Matrix.diagonal_mul]

theorem prod_abs_rotated_cpow (s : Fin n → ℂ) {N : ℕ} (hs : s (ia h) - s (ib h) = N)
    (hb : b.IsUpperTriangular) (hρ : 0 < ρ)
    (hρ2 : ρ ^ 2 = bottomRight h b θ ^ 2 + bottomLeft h b θ ^ 2)
    (hu : Real.cos φ * ρ = bottomRight h b θ) (hv : Real.sin φ * ρ = bottomLeft h b θ) :
    ∏ l : Fin n, ((|rotated h b θ φ l l| : ℝ) : ℂ) ^ s l =
      (∏ l : Fin n, ((baseWeight h b l : ℝ) : ℂ) ^ s l) * ((ρ : ℂ) ^ N)⁻¹ := by
  have hne := ia_ne_ib h
  have hρC : (ρ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hρ.ne'
  have harg : (ρ : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hρ.le]
    exact Real.pi_ne_zero.symm
  have hX0 : (ρ : ℂ) ^ s (ia h) ≠ 0 := fun h0 => hρC ((Complex.cpow_eq_zero_iff _ _).mp h0).1
  have hterm : ∀ l : Fin n, ((|rotated h b θ φ l l| : ℝ) : ℂ) ^ s l =
      ((baseWeight h b l : ℝ) : ℂ) ^ s l *
        ((if l = ia h then ((ρ : ℂ) ^ s (ia h))⁻¹ else 1) *
          (if l = ib h then (ρ : ℂ) ^ s (ib h) else 1)) := by
    intro l
    by_cases h1 : l = ia h
    · subst h1
      simp only [baseWeight, hne, ite_true, ite_false, mul_one]
      rw [rotated_ia_eq h hb hρ hu hv, abs_mul _ ρ⁻¹, abs_inv, abs_of_pos hρ, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg (abs_nonneg _) (inv_nonneg.mpr hρ.le), Complex.ofReal_inv,
        Complex.inv_cpow _ _ harg]
    · by_cases h2 : l = ib h
      · subst h2
        simp only [baseWeight, hne.symm, ite_true, ite_false, one_mul]
        rw [rotated_ib h hb hρ hρ2 hu hv, abs_of_pos hρ, Complex.ofReal_one, Complex.one_cpow,
          one_mul]
      · simp only [baseWeight, h1, h2, ite_false, mul_one]
        rw [rotated_apply_self_of_ne h h1 h2]
  rw [Finset.prod_congr rfl fun l _ => hterm l, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  simp only [Finset.prod_ite_eq', Finset.mem_univ, ite_true]
  congr 1
  rw [show s (ib h) = s (ia h) - N by rw [← hs]; ring, Complex.cpow_sub _ _ hρC,
    Complex.cpow_natCast, mul_div_assoc', inv_mul_cancel₀ hX0, one_div]

/-- **The Gram function along the rotations.** For `g = b κ` and `P = Φ_p · R` with `R` free of
the rows `p, p + 1` and `s_p - s_{p+1} = N`, the value at `r(θ) g` is
`C (L₊^N (d' + iσc')^(-N) + (-1)^N L₋^N (d' - iσc')^(-N))`, with `C`, `L₊`, `L₋` independent
of `θ`. -/
theorem gramFunction_blockRotation_eq (s : Fin n → ℂ) {N : ℕ} (hs : s (ia h) - s (ib h) = N)
    {R : MvPolynomial (Fin n × Fin n) ℂ} (hR : DependsOnRows {l | l ≠ p ∧ l ≠ p + 1} R)
    (hb : b.IsUpperTriangular) (hd : ∀ l, b l l ≠ 0) {κ : Matrix (Fin n) (Fin n) ℝ}
    (hκ : κ ∈ Matrix.unitaryGroup (Fin n) ℝ) {g : Langlands.GeneralLinear n ℝ}
    (hg : (g : Matrix (Fin n) (Fin n) ℝ) = b * κ) (θ : ℝ) :
    gramFunction s (blockFactor n p N * R) (blockRotation n p θ * g) =
      (∏ l : Fin n, ((baseWeight h b l : ℝ) : ℂ) ^ s l) *
        MvPolynomial.eval (baseEntries h b κ) R *
        (MvPolynomial.eval (baseEntries h b κ) (lplus n p) ^ N *
            ((((bottomRight h b θ : ℝ) : ℂ) +
              Complex.I * ((blockSign h b * bottomLeft h b θ : ℝ) : ℂ)) ^ N)⁻¹ +
          (-1) ^ N * MvPolynomial.eval (baseEntries h b κ) (lminus n p) ^ N *
            ((((bottomRight h b θ : ℝ) : ℂ) -
              Complex.I * ((blockSign h b * bottomLeft h b θ : ℝ) : ℂ)) ^ N)⁻¹) := by
  obtain ⟨φ, ρ, hρ, hρ2, hu, hv⟩ := exists_polar (bottom_ne_zero h hd θ)
  rw [gramFunction_blockRotation_mul h s _ hb hd hκ hg hρ hρ2 hu hv,
    prod_abs_rotated_cpow h s hs hb hρ hρ2 hu hv,
    eval_rotated_blockFactor_mul h N hR (isRowRotation_rotated h hb hd hρ hρ2 hu hv κ)]
  have hσ := blockSign_sq h (b := b)
  have huv : Real.cos φ ^ 2 + (blockSign h b * Real.sin φ) ^ 2 = 1 := by
    linear_combination Real.cos_sq_add_sin_sq φ + Real.sin φ ^ 2 * hσ
  have huv' : Real.cos φ ^ 2 + (-(blockSign h b * Real.sin φ)) ^ 2 = 1 := by
    linear_combination huv
  have e1 := inv_pow_mul_sub_eq hρ.ne' huv hu
    (show blockSign h b * Real.sin φ * ρ = blockSign h b * bottomLeft h b θ by
      rw [mul_assoc, hv]) N
  have e2 := inv_pow_mul_add_eq hρ.ne' huv hu
    (show blockSign h b * Real.sin φ * ρ = blockSign h b * bottomLeft h b θ by
      rw [mul_assoc, hv]) N
  rw [← e1, ← e2]
  ring

end Value

/-! ## The Fourier coefficients -/

theorem bottom_add_eq (θ : ℝ) :
    ((bottomRight h b θ : ℝ) : ℂ) + Complex.I * ((blockSign h b * bottomLeft h b θ : ℝ) : ℂ) =
      Analysis.InversePowerFourier.rotP (-(blockSign h b * b (ia h) (ia h))) (b (ia h) (ib h)) 0
          (b (ib h) (ib h)) * Complex.exp (θ * Complex.I) +
        Analysis.InversePowerFourier.rotQ (-(blockSign h b * b (ia h) (ia h))) (b (ia h) (ib h)) 0
          (b (ib h) (ib h)) * Complex.exp (-(θ * Complex.I)) := by
  rw [← Analysis.InversePowerFourier.rotated_bottom_eq, bottomRight, bottomLeft]
  push_cast
  ring

theorem bottom_sub_eq (θ : ℝ) :
    ((bottomRight h b θ : ℝ) : ℂ) - Complex.I * ((blockSign h b * bottomLeft h b θ : ℝ) : ℂ) =
      Analysis.InversePowerFourier.rotP (blockSign h b * b (ia h) (ia h)) (b (ia h) (ib h)) 0
          (b (ib h) (ib h)) * Complex.exp (θ * Complex.I) +
        Analysis.InversePowerFourier.rotQ (blockSign h b * b (ia h) (ia h)) (b (ia h) (ib h)) 0
          (b (ib h) (ib h)) * Complex.exp (-(θ * Complex.I)) := by
  rw [← Analysis.InversePowerFourier.rotated_bottom_eq, bottomRight, bottomLeft]
  push_cast
  ring

/-- **Fourier vanishing at an induction block.** If `P = Φ_p · R` with `Φ_p` of degree `N`, `R`
free of the rows `p, p + 1` and `s_p - s_{p+1} = N`, the Gram function has no Fourier modes of
weight `|k| < N` along the rotations in the coordinates `p, p + 1`. -/
theorem blockFourierCoefficient_eq_zero (s : Fin n → ℂ) {N : ℕ} (hs : s (ia h) - s (ib h) = N)
    {R : MvPolynomial (Fin n × Fin n) ℂ} (hR : DependsOnRows {l | l ≠ p ∧ l ≠ p + 1} R) {k : ℤ}
    (hk : |k| < N) (g : Langlands.GeneralLinear n ℝ) :
    blockFourierCoefficient n p k (gramFunction s (blockFactor n p N * R)) g = 0 := by
  obtain ⟨a, u, c, hc, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitaryCompact g
  set b : Matrix (Fin n) (Fin n) ℝ := Matrix.diagonal (fun l => (a l : ℝ)) *
    ((u : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) with hbdef
  have hb : b.IsUpperTriangular := GramFormula.isUpperTriangular_diagonal_mul a u
  have hd : ∀ l, b l l ≠ 0 := fun l => by
    rw [hbdef, GramFormula.diagonal_mul_apply_self]
    exact (a l).ne_zero
  have hg : (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
      (u : Langlands.GeneralLinear n ℝ) * c : Langlands.GeneralLinear n ℝ) :
        Matrix (Fin n) (Fin n) ℝ) = b * (c : Matrix (Fin n) (Fin n) ℝ) := rfl
  have hσ0 : blockSign h b ≠ 0 := fun h0 => by
    have := blockSign_sq h (b := b)
    rw [h0] at this
    norm_num at this
  have hn1 := Analysis.InversePowerFourier.norm_rotP_ne_norm_rotQ
    (a := -(blockSign h b * b (ia h) (ia h))) (b := b (ia h) (ib h)) (c := 0)
    (d := b (ib h) (ib h)) (by
      rw [mul_zero, sub_zero]
      exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero hσ0 (hd _))) (hd _))
  have hn2 := Analysis.InversePowerFourier.norm_rotP_ne_norm_rotQ
    (a := blockSign h b * b (ia h) (ia h)) (b := b (ia h) (ib h)) (c := 0)
    (d := b (ib h) (ib h)) (by
      rw [mul_zero, sub_zero]
      exact mul_ne_zero (mul_ne_zero hσ0 (hd _)) (hd _))
  set C : ℂ := (∏ l : Fin n, ((baseWeight h b l : ℝ) : ℂ) ^ s l) *
    MvPolynomial.eval (baseEntries h b c) R with hC
  set C₁ : ℂ := C * MvPolynomial.eval (baseEntries h b c) (lplus n p) ^ N with hC₁
  set C₂ : ℂ := C * ((-1) ^ N * MvPolynomial.eval (baseEntries h b c) (lminus n p) ^ N) with hC₂
  have hfun : (fun θ : ℝ => gramFunction s (blockFactor n p N * R)
      (blockRotation n p θ * ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℝ) *
        (u : Langlands.GeneralLinear n ℝ) * c)) * Complex.exp (-((k : ℂ) * (θ : ℂ) * Complex.I))) =
      fun θ => C₁ * Analysis.InversePowerFourier.integrand
          (Analysis.InversePowerFourier.rotP (-(blockSign h b * b (ia h) (ia h)))
            (b (ia h) (ib h)) 0 (b (ib h) (ib h)))
          (Analysis.InversePowerFourier.rotQ (-(blockSign h b * b (ia h) (ia h)))
            (b (ia h) (ib h)) 0 (b (ib h) (ib h))) N k θ +
        C₂ * Analysis.InversePowerFourier.integrand
          (Analysis.InversePowerFourier.rotP (blockSign h b * b (ia h) (ia h))
            (b (ia h) (ib h)) 0 (b (ib h) (ib h)))
          (Analysis.InversePowerFourier.rotQ (blockSign h b * b (ia h) (ia h))
            (b (ia h) (ib h)) 0 (b (ib h) (ib h))) N k θ := by
    funext θ
    rw [gramFunction_blockRotation_eq h s hs hR hb hd (κ := (c : Matrix (Fin n) (Fin n) ℝ)) hc hg θ,
      bottom_add_eq h θ,
      bottom_sub_eq h θ]
    unfold Analysis.InversePowerFourier.integrand
    rw [hC₁, hC₂, hC]
    ring
  unfold blockFourierCoefficient
  rw [hfun, intervalIntegral.integral_add,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    Analysis.InversePowerFourier.integral_integrand_eq_zero hn1 N hk,
    Analysis.InversePowerFourier.integral_integrand_eq_zero hn2 N hk, mul_zero, mul_zero, add_zero]
  · exact (continuous_const.mul
      (Analysis.InversePowerFourier.continuous_integrand hn1 N k)).intervalIntegrable _ _
  · exact (continuous_const.mul
      (Analysis.InversePowerFourier.continuous_integrand hn2 N k)).intervalIntegrable _ _

end RealStandardNontrivial

/-! ## Real standard modules are nonzero -/

open RealStandardNontrivial in
/-- The Gram function of the block polynomial is an `O(n)`-finite function of the real standard
module. -/
theorem gramFunction_blockPoly_mem (n : ℕ) (ds : List RealBlock) (hds : realRank ds = n) :
    gramFunction (shiftedExponent n (realPositionExponent ds)) (blockPoly n ds 0) ∈
      kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) := by
  have hK := gramFunction_mem_kFiniteFunctions (realPositionExponent ds)
    (realPositionCharacter_eq_signUnit_mul ds) (hasSignParity_blockPoly ds hds)
  refine ⟨(mem_realStandardModule_iff _ _ _).mpr ⟨hK.1, ?_⟩, hK.2⟩
  intro p d hpd k hk g
  have h : p + 1 < n := hds ▸ realInducedBlockAt_lt hpd
  obtain ⟨R, hP, hR⟩ := exists_blockPoly_eq_blockFactor_mul (n := n) ds 0 p d hpd
  simp only [zero_add] at hP hR
  rw [hP]
  refine blockFourierCoefficient_eq_zero h _ ?_ hR ?_ g
  · have he := realPositionExponent_of_blockAt hpd
    simp only [shiftedExponent, val_ia, val_ib]
    push_cast
    linear_combination he
  · have h2 : ((d.weight.natAbs : ℕ) : ℤ) = |d.weight| := Int.natCast_natAbs _
    push_cast
    linarith

/-- **Real standard modules are nonzero**: for real blocks `ds` of total rank `n`, the
`O(n)`-finite functions of the real standard module `realStandardModule n ds` form a nonzero
space. -/
theorem realStandardNontrivial : ∀ (n : ℕ) (ds : List RealBlock), realRank ds = n →
    Nontrivial (kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) := by
  intro n ds hds
  refine nontrivial_of_ne ⟨_, gramFunction_blockPoly_mem n ds hds⟩ 0 ?_
  intro h0
  have h1 := congrArg (fun x : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) =>
    (x : Langlands.GeneralLinear n ℝ → ℂ) 1) h0
  simp only [ZeroMemClass.coe_zero, Pi.zero_apply] at h1
  rw [gramFunction_one] at h1
  exact RealStandardNontrivial.eval_one_blockPoly_ne_zero ds 0 (by omega) h1

end Langlands.Archimedean
