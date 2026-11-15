import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar
import Langlands.Representation.Archimedean.PrincipalSeriesStability
import Langlands.LinearAlgebra.TriangularUnitary

/-!
# Nondegeneracy of the integration pairing on `U(n)`

For characters `χ, χ'` with `χᵢ χ'ᵢ = 1` and `|χᵢ(z)|² = |z|^(2 sᵢ)`, every nonzero `U(n)`-finite
function `h` of the principal series of `χ'` pairs nontrivially with the `U(n)`-finite function
`ψ · conj h` of the principal series of `χ`, where `ψ` is a product of powers of ratios of Gram
determinants of the lower rows: on `U(n)` the integrand is `|h|²`.
-/

noncomputable section

open scoped Matrix Matrix.Norms.Operator ContDiff Manifold ComplexConjugate
open MeasureTheory

namespace Langlands.Archimedean.ComplexDuality

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

/-! ## Iwasawa decomposition of `GL_n(ℂ)` -/

/-- Every `g ∈ GL_n(ℂ)` is `diag(a) · u · k` with `a : Fin n → ℂˣ`, `u` upper unipotent and
`k ∈ U(n)`. -/
theorem exists_diagonalUnits_mul_upperUnipotent_mul_unitary
    (g : Langlands.GeneralLinear n ℂ) :
    ∃ (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) (k : Langlands.GeneralLinear n ℂ),
      k ∈ unitaryCompact ℂ n ∧
        g = (Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
          (u : Langlands.GeneralLinear n ℂ) * k := by
  obtain ⟨b, w, hb, hbu, hw, hg⟩ :=
    Langlands.LinearAlgebra.TriangularUnitary.exists_upperTriangular_mul_unitary
      (g : Matrix (Fin n) (Fin n) ℂ) g.isUnit
  have hdet : b.det = ∏ i, b i i := Matrix.det_of_isUpperTriangular hb
  have hdiag : ∀ i, b i i ≠ 0 := by
    have h0 : b.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det b).mp hbu).ne_zero
    rw [hdet] at h0
    exact fun i => Finset.prod_ne_zero_iff.mp h0 i (Finset.mem_univ i)
  let a : Fin n → ℂˣ := fun i => Units.mk0 (b i i) (hdiag i)
  let B : Langlands.GeneralLinear n ℂ := hbu.unit
  let D : Langlands.GeneralLinear n ℂ := Iwasawa.diagonalUnits a
  have hDinv : ((D⁻¹ : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal fun i => (b i i)⁻¹ := by
    rfl
  have hu : D⁻¹ * B ∈ upperUnipotent n ℂ := by
    have hval : ((D⁻¹ * B : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal (fun i => (b i i)⁻¹) * b := by
      rw [Units.val_mul, hDinv]
      rfl
    refine ⟨?_, fun i => ?_⟩
    · change ((D⁻¹ * B : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ).BlockTriangular id
      rw [hval]
      exact (Matrix.blockTriangular_diagonal _).mul hb
    · change ((D⁻¹ * B : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) i i = 1
      rw [hval, Matrix.diagonal_mul]
      exact inv_mul_cancel₀ (hdiag i)
  let k : Langlands.GeneralLinear n ℂ := Unitary.toUnits ⟨w, hw⟩
  refine ⟨a, ⟨D⁻¹ * B, hu⟩, k, hw, ?_⟩
  apply Units.ext
  change (g : Matrix (Fin n) (Fin n) ℂ) = ((D * (D⁻¹ * B) * k : Langlands.GeneralLinear n ℂ) :
    Matrix (Fin n) (Fin n) ℂ)
  rw [mul_inv_cancel_left]
  rw [hg]
  rfl

/-- A function of the principal series of `GL_n(ℂ)` vanishing on `U(n)` vanishes. -/
theorem eq_zero_of_mem_principalSeries_of_eqOn {χ : ℕ → ℂˣ → ℂ}
    {f : Langlands.GeneralLinear n ℂ → ℂ} (hf : f ∈ principalSeries ℂ n χ)
    (h : ∀ k ∈ unitaryCompact ℂ n, f k = 0) : f = 0 := by
  funext g
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  rw [hf.2 a u k, h k hk, mul_zero]
  rfl

/-! ## Gram determinants of the lower rows -/

/-- The rows `m, …, n-1` of a square matrix. -/
def tailRows (m : ℕ) (y : Matrix (Fin n) (Fin n) ℂ) :
    Matrix {j : Fin n // m ≤ (j : ℕ)} (Fin n) ℂ :=
  Matrix.of fun i j => y i j

/-- The Gram determinant `det (Y Yᴴ)` of the rows `m, …, n-1` of `y`. -/
def tailGram (m : ℕ) (y : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (tailRows m y * (tailRows m y)ᴴ).det

theorem tailRows_mul (m : ℕ) (y x : Matrix (Fin n) (Fin n) ℂ) :
    tailRows m (y * x) = tailRows m y * x := by
  ext i j
  simp [tailRows, Matrix.mul_apply]

theorem tailGram_mul_unitary (m : ℕ) (y : Matrix (Fin n) (Fin n) ℂ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    tailGram m (y * k) = tailGram m y := by
  have hk' : k * kᴴ = 1 := by
    have := Matrix.mem_unitaryGroup_iff.mp hk
    rwa [Matrix.star_eq_conjTranspose] at this
  have : tailRows m (y * k) * (tailRows m (y * k))ᴴ = tailRows m y * (k * kᴴ) *
      (tailRows m y)ᴴ := by
    rw [tailRows_mul, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [tailGram, this, hk', Matrix.mul_one, tailGram]

theorem tailGram_one (m : ℕ) : tailGram m (1 : Matrix (Fin n) (Fin n) ℂ) = 1 := by
  have : tailRows m (1 : Matrix (Fin n) (Fin n) ℂ) *
      (tailRows m (1 : Matrix (Fin n) (Fin n) ℂ))ᴴ =
        (1 : Matrix {j : Fin n // m ≤ (j : ℕ)} {j : Fin n // m ≤ (j : ℕ)} ℂ) := by
    ext i i'
    simp only [tailRows, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Matrix.one_apply]
    simp [Subtype.ext_iff, eq_comm]
  rw [tailGram, this, Matrix.det_one]

theorem tailRows_upper_mul (m : ℕ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular)
    (y : Matrix (Fin n) (Fin n) ℂ) :
    tailRows m (b * y) =
      b.submatrix (Subtype.val : {j : Fin n // m ≤ (j : ℕ)} → Fin n) Subtype.val *
        tailRows m y := by
  ext i j
  simp only [tailRows, Matrix.of_apply, Matrix.mul_apply, Matrix.submatrix_apply]
  have hz : ∑ k : {k : Fin n // ¬ m ≤ (k : ℕ)}, b i (k : Fin n) * y (k : Fin n) j = 0 :=
    Finset.sum_eq_zero fun k _ => by
      have hk : (k : Fin n) < (i : Fin n) := by
        have h1 := k.2
        have h2 := i.2
        rw [Fin.lt_def]
        omega
      rw [hb hk, zero_mul]
  rw [← Fintype.sum_subtype_add_sum_subtype (fun k : Fin n => m ≤ (k : ℕ)), hz, add_zero]

theorem det_submatrix_tail {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular) (m : ℕ) :
    (b.submatrix (Subtype.val : {j : Fin n // m ≤ (j : ℕ)} → Fin n) Subtype.val).det =
      ∏ i : {j : Fin n // m ≤ (j : ℕ)}, b i i := by
  rw [Matrix.det_of_isUpperTriangular]
  · rfl
  · intro i j hij
    exact hb hij

theorem tailGram_upper_mul (m : ℕ) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsUpperTriangular)
    (y : Matrix (Fin n) (Fin n) ℂ) :
    tailGram m (b * y) =
      ((∏ i : {j : Fin n // m ≤ (j : ℕ)}, Complex.normSq (b i i) : ℝ) : ℂ) * tailGram m y := by
  set B := b.submatrix (Subtype.val : {j : Fin n // m ≤ (j : ℕ)} → Fin n) Subtype.val
  have : tailRows m (b * y) * (tailRows m (b * y))ᴴ =
      B * (tailRows m y * (tailRows m y)ᴴ) * Bᴴ := by
    rw [tailRows_upper_mul m hb, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
    rfl
  have hd : ((∏ i : {j : Fin n // m ≤ (j : ℕ)}, Complex.normSq (b i i) : ℝ) : ℂ) =
      B.det * star B.det := by
    rw [det_submatrix_tail hb, ← map_prod Complex.normSq, ← Complex.mul_conj]
    rfl
  rw [tailGram, this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, hd, tailGram]
  ring

/-- The upper triangular matrix `diag(a) u` in matrix form. -/
theorem val_diagonalUnits_mul (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ) :
    (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) =
      Matrix.diagonal (fun i => (a i : ℂ)) *
        ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) :=
  rfl

theorem tailGram_borel_mul (m : ℕ) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    (y : Matrix (Fin n) (Fin n) ℂ) :
    tailGram m ((((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) * y) =
      ((∏ i : {j : Fin n // m ≤ (j : ℕ)}, Complex.normSq (a i : ℂ) : ℝ) : ℂ) *
        tailGram m y := by
  have hb : (Matrix.diagonal (fun i => (a i : ℂ)) *
      ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)).IsUpperTriangular :=
    (Matrix.blockTriangular_diagonal _).mul u.2.1
  rw [val_diagonalUnits_mul, tailGram_upper_mul m hb]
  congr 3
  funext i
  rw [Matrix.diagonal_mul, u.2.2 i, mul_one]

/-- On `GL_n(ℂ)` the Gram determinant of the lower rows is a positive real number. -/
theorem exists_tailGram_eq_pos (m : ℕ) (g : Langlands.GeneralLinear n ℂ) :
    ∃ r : ℝ, 0 < r ∧ tailGram m (g : Matrix (Fin n) (Fin n) ℂ) = r := by
  obtain ⟨a, u, k, hk, rfl⟩ := exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  refine ⟨∏ i : {j : Fin n // m ≤ (j : ℕ)}, Complex.normSq (a i : ℂ),
    Finset.prod_pos fun i _ => Complex.normSq_pos.mpr (a i).ne_zero, ?_⟩
  rw [Units.val_mul, tailGram_borel_mul, ← Matrix.one_mul (k : Matrix (Fin n) (Fin n) ℂ),
    tailGram_mul_unitary _ _ hk, tailGram_one, mul_one]

/-- The real part of the Gram determinant of the rows `m, …, n-1`. -/
def gramMinor (m : ℕ) (y : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  (tailGram m y).re

theorem ofReal_gramMinor (m : ℕ) (g : Langlands.GeneralLinear n ℂ) :
    ((gramMinor m (g : Matrix (Fin n) (Fin n) ℂ) : ℝ) : ℂ) =
      tailGram m (g : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨r, -, hr⟩ := exists_tailGram_eq_pos m g
  rw [gramMinor, hr, Complex.ofReal_re]

theorem gramMinor_pos (m : ℕ) (g : Langlands.GeneralLinear n ℂ) :
    0 < gramMinor m (g : Matrix (Fin n) (Fin n) ℂ) := by
  obtain ⟨r, hr0, hr⟩ := exists_tailGram_eq_pos m g
  rw [gramMinor, hr, Complex.ofReal_re]
  exact hr0

theorem prod_tail_succ (m : Fin n) (c : Fin n → ℝ) :
    ∏ i : {j : Fin n // (m : ℕ) ≤ (j : ℕ)}, c i =
      c m * ∏ i : {j : Fin n // (m : ℕ) + 1 ≤ (j : ℕ)}, c i := by
  rw [← Finset.prod_subtype (Finset.univ.filter fun j : Fin n => (m : ℕ) ≤ (j : ℕ))
      (by simp) c,
    ← Finset.prod_subtype (Finset.univ.filter fun j : Fin n => (m : ℕ) + 1 ≤ (j : ℕ))
      (by simp) c]
  have : Finset.univ.filter (fun j : Fin n => (m : ℕ) ≤ (j : ℕ)) =
      insert m (Finset.univ.filter fun j : Fin n => (m : ℕ) + 1 ≤ (j : ℕ)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  rw [this, Finset.prod_insert (by simp)]

/-! ## The Gram weight -/

/-- The weight `ψ_s(y) = ∏ₘ (Rₘ(y) / Rₘ₊₁(y))^(sₘ)`, with `Rₘ` the Gram determinant of the
rows `m, …, n-1` (and `Rₙ = 1`). -/
def gramWeight (s : ℕ → ℝ) (y : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∏ m : Fin n, (gramMinor (m : ℕ) y / gramMinor ((m : ℕ) + 1) y) ^ s m

theorem gramWeight_mul_unitary (s : ℕ → ℝ) (y : Matrix (Fin n) (Fin n) ℂ)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    gramWeight s (y * k) = gramWeight s y := by
  simp only [gramWeight, gramMinor, tailGram_mul_unitary _ _ hk]

theorem gramWeight_unitary (s : ℕ → ℝ) {k : Matrix (Fin n) (Fin n) ℂ}
    (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) : gramWeight s k = 1 := by
  rw [← Matrix.one_mul k, gramWeight_mul_unitary s _ hk]
  simp [gramWeight, gramMinor, tailGram_one]

theorem gramMinor_borel_mul (m : ℕ) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    (y : Matrix (Fin n) (Fin n) ℂ) :
    gramMinor m ((((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) * y) =
      (∏ i : {j : Fin n // m ≤ (j : ℕ)}, Complex.normSq (a i : ℂ)) * gramMinor m y := by
  rw [gramMinor, tailGram_borel_mul, Complex.re_ofReal_mul, gramMinor]

theorem gramWeight_borel_mul (s : ℕ → ℝ) (a : Fin n → ℂˣ) (u : upperUnipotent n ℂ)
    (g : Langlands.GeneralLinear n ℂ) :
    gramWeight s (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) =
      (∏ m : Fin n, Complex.normSq (a m : ℂ) ^ s m) *
        gramWeight s (g : Matrix (Fin n) (Fin n) ℂ) := by
  rw [Units.val_mul, gramWeight, gramWeight, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun m _ => ?_
  rw [gramMinor_borel_mul, gramMinor_borel_mul,
    prod_tail_succ m (fun i => Complex.normSq (a i : ℂ))]
  have hP : 0 < ∏ i : {j : Fin n // (m : ℕ) + 1 ≤ (j : ℕ)}, Complex.normSq (a i : ℂ) :=
    Finset.prod_pos fun i _ => Complex.normSq_pos.mpr (a i).ne_zero
  have h1 := gramMinor_pos (m : ℕ) g
  have h2 := gramMinor_pos ((m : ℕ) + 1) g
  have hratio :
      Complex.normSq (a m : ℂ) *
          (∏ i : {j : Fin n // (m : ℕ) + 1 ≤ (j : ℕ)}, Complex.normSq (a i : ℂ)) *
          gramMinor (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) /
        ((∏ i : {j : Fin n // (m : ℕ) + 1 ≤ (j : ℕ)}, Complex.normSq (a i : ℂ)) *
          gramMinor ((m : ℕ) + 1) (g : Matrix (Fin n) (Fin n) ℂ)) =
      Complex.normSq (a m : ℂ) *
        (gramMinor (m : ℕ) (g : Matrix (Fin n) (Fin n) ℂ) /
          gramMinor ((m : ℕ) + 1) (g : Matrix (Fin n) (Fin n) ℂ)) := by
    field_simp
  rw [hratio, Real.mul_rpow (Complex.normSq_nonneg _) (div_pos h1 h2).le]

/-! ## Smoothness of the Gram weight -/

theorem contDiff_tailGram (m : ℕ) :
    ContDiff ℝ ∞ (tailGram m : Matrix (Fin n) (Fin n) ℂ → ℂ) := by
  have hentry : ∀ i j : Fin n,
      ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ => y i j) := by
    intro i j
    let e : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℂ :=
      { toFun := fun y => y i j
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    exact (LinearMap.toContinuousLinearMap e).contDiff
  have hG : ∀ i i' : {j : Fin n // m ≤ (j : ℕ)},
      ContDiff ℝ ∞ (fun y : Matrix (Fin n) (Fin n) ℂ =>
        (tailRows m y * (tailRows m y)ᴴ) i i') := by
    intro i i'
    simp only [Matrix.mul_apply, tailRows, Matrix.conjTranspose_apply, Matrix.of_apply]
    exact ContDiff.sum fun k _ =>
      (hentry i k).mul (Complex.conjCLE.contDiff.comp (hentry i' k))
  unfold tailGram
  simp_rw [Matrix.det_apply']
  exact ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => hG (σ i) i)

theorem contDiffAt_gramWeight (s : ℕ → ℝ) (g : Langlands.GeneralLinear n ℂ) :
    ContDiffAt ℝ ∞ (gramWeight s) (g : Matrix (Fin n) (Fin n) ℂ) := by
  have hre : ∀ m : ℕ, ContDiff ℝ ∞ (gramMinor m : Matrix (Fin n) (Fin n) ℂ → ℝ) :=
    fun m => Complex.reCLM.contDiff.comp (contDiff_tailGram m)
  unfold gramWeight
  refine contDiffAt_prod fun m _ => ?_
  refine ContDiffAt.rpow_const_of_ne ?_ ?_
  · exact ((hre m).contDiffAt).div ((hre ((m : ℕ) + 1)).contDiffAt) (gramMinor_pos _ g).ne'
  · exact (div_pos (gramMinor_pos _ g) (gramMinor_pos _ g)).ne'

/-! ## The partner function -/

/-- The partner `ψ_s · conj h` of a function `h` on `GL_n(ℂ)`. -/
def partner (s : ℕ → ℝ) (h : Langlands.GeneralLinear n ℂ → ℂ)
    (g : Langlands.GeneralLinear n ℂ) : ℂ :=
  (gramWeight s (g : Matrix (Fin n) (Fin n) ℂ) : ℂ) * star (h g)

theorem conj_cpow_ofReal {r : ℝ} (hr : 0 ≤ r) (N i : ℕ) :
    conj ((r : ℂ) ^ (((N : ℂ) - 1) / 2 - (i : ℂ))) = (r : ℂ) ^ (((N : ℂ) - 1) / 2 - (i : ℂ)) := by
  have : ((N : ℂ) - 1) / 2 - (i : ℂ) = ((((N : ℝ) - 1) / 2 - i : ℝ) : ℂ) := by
    push_cast
    ring
  rw [this, ← Complex.ofReal_cpow hr, Complex.conj_ofReal]

/-- `|χ(a)|² · conj (character of χ') = character of χ` when `χᵢ χ'ᵢ = 1`. -/
theorem normSq_mul_star_principalSeriesCharacter {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ : ∀ i z, χ i z * χ' i z = 1) {s : ℕ → ℝ}
    (hs : ∀ i (z : ℂˣ), Complex.normSq (χ i z) = Complex.normSq (z : ℂ) ^ s i)
    (a : Fin n → ℂˣ) :
    (((∏ m : Fin n, Complex.normSq (a m : ℂ) ^ s m : ℝ)) : ℂ) *
        star (principalSeriesCharacter ℂ n χ' a) =
      principalSeriesCharacter ℂ n χ a := by
  unfold principalSeriesCharacter
  rw [Complex.ofReal_prod, Complex.star_def, map_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [map_mul, conj_cpow_ofReal (pow_nonneg (norm_nonneg _) _), ← hs, ← Complex.mul_conj]
  calc χ i (a i) * conj (χ i (a i)) *
        (conj (χ' i (a i)) *
          ((‖(a i : ℂ)‖ ^ Module.finrank ℝ ℂ : ℝ) : ℂ) ^ (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)))
      = χ i (a i) * conj (χ i (a i) * χ' i (a i)) *
          ((‖(a i : ℂ)‖ ^ Module.finrank ℝ ℂ : ℝ) : ℂ) ^
            (((n : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)) := by
        rw [map_mul]
        ring
    _ = _ := by rw [hχ, map_one, mul_one]

theorem partner_mem_principalSeries {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ : ∀ i z, χ i z * χ' i z = 1) {s : ℕ → ℝ}
    (hs : ∀ i (z : ℂˣ), Complex.normSq (χ i z) = Complex.normSq (z : ℂ) ^ s i)
    {h : Langlands.GeneralLinear n ℂ → ℂ} (hh : h ∈ principalSeries ℂ n χ') :
    partner s h ∈ principalSeries ℂ n χ := by
  refine ⟨?_, fun a u g => ?_⟩
  · refine contMDiff_of_contDiffOn
      (ψ := fun y => (gramWeight s y : ℂ) * star (unitsExtension h y)) ?_ ?_
    · intro y hy
      obtain ⟨g, rfl⟩ := hy
      have h1 : ContDiffAt ℝ ∞ (fun y => (gramWeight s y : ℂ)) (g : Matrix (Fin n) (Fin n) ℂ) :=
        Complex.ofRealCLM.contDiff.contDiffAt.comp _ (contDiffAt_gramWeight s g)
      have h2 := Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_unitsExtension hh.1)
        _ (Units.isUnit g)
      exact h1.contDiffWithinAt.mul h2
    · intro g
      simp only [partner, unitsExtension_val]
  · change ((gramWeight s (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
        (u : Langlands.GeneralLinear n ℂ) * g : Langlands.GeneralLinear n ℂ) :
          Matrix (Fin n) (Fin n) ℂ) : ℝ) : ℂ) *
        star (h ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) *
          (u : Langlands.GeneralLinear n ℂ) * g)) =
      principalSeriesCharacter ℂ n χ a * partner s h g
    rw [hh.2 a u g, gramWeight_borel_mul, Complex.ofReal_mul, star_mul',
      ← normSq_mul_star_principalSeriesCharacter hχ hs a, partner]
    ring

theorem partner_rightTranslation (s : ℕ → ℝ) (h : Langlands.GeneralLinear n ℂ → ℂ)
    {k : Langlands.GeneralLinear n ℂ} (hk : k ∈ unitaryCompact ℂ n) :
    Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k (partner s h) =
      partner s (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) k h) := by
  funext g
  change partner s h (g * k) = partner s (fun x => h (x * k)) g
  simp only [partner, Units.val_mul, gramWeight_mul_unitary s _ hk]

theorem partner_zero (s : ℕ → ℝ) :
    partner s (0 : Langlands.GeneralLinear n ℂ → ℂ) = 0 := by
  funext g
  simp [partner]

theorem partner_add (s : ℕ → ℝ) (h₁ h₂ : Langlands.GeneralLinear n ℂ → ℂ) :
    partner s (h₁ + h₂) = partner s h₁ + partner s h₂ := by
  funext g
  simp [partner, mul_add]

theorem partner_smul (s : ℕ → ℝ) (c : ℂ) (h : Langlands.GeneralLinear n ℂ → ℂ) :
    partner s (c • h) = star c • partner s h := by
  funext g
  simp only [partner, Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem partner_mem_span (s : ℕ → ℝ) (S : Set (Langlands.GeneralLinear n ℂ → ℂ))
    {v : Langlands.GeneralLinear n ℂ → ℂ} (hv : v ∈ Submodule.span ℂ S) :
    partner s v ∈ Submodule.span ℂ (partner s '' S) := by
  induction hv using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [partner_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [partner_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [partner_smul]; exact Submodule.smul_mem _ _ hx

theorem partner_mem_kFiniteVectors (s : ℕ → ℝ) {h : Langlands.GeneralLinear n ℂ → ℂ}
    (hh : h ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n)) :
    partner s h ∈ kFiniteVectors (Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ))
      (unitaryCompact ℂ n) := by
  rw [mem_kFiniteVectors_iff] at hh ⊢
  obtain ⟨S, hSfin, hS⟩ := Submodule.fg_def.mp
    ((Submodule.fg_iff_finiteDimensional _).mpr hh)
  have hle : Submodule.span ℂ (Set.range fun k : unitaryCompact ℂ n =>
      Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℂ) (k : Langlands.GeneralLinear n ℂ)
        (partner s h)) ≤ Submodule.span ℂ (partner s '' S) := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    beta_reduce
    rw [partner_rightTranslation s h k.2]
    apply partner_mem_span
    rw [hS]
    exact Submodule.subset_span ⟨k, rfl⟩
  have := FiniteDimensional.span_of_finite ℂ (hSfin.image (partner s))
  exact Submodule.finiteDimensional_of_le hle

/-! ## Nondegeneracy -/

/-- For `χᵢ χ'ᵢ = 1` and `|χᵢ(z)|² = |z|^(2 sᵢ)`, every nonzero `U(n)`-finite function `h` of the
principal series of `χ'` has a `U(n)`-finite partner `f` in the principal series of `χ` with
`∫_{U(n)} f h ≠ 0`. -/
theorem exists_integral_mul_ne_zero {χ χ' : ℕ → ℂˣ → ℂ}
    (hχ : ∀ i z, χ i z * χ' i z = 1) {s : ℕ → ℝ}
    (hs : ∀ i (z : ℂˣ), Complex.normSq (χ i z) = Complex.normSq (z : ℂ) ^ s i)
    (h : kFiniteFunctions (principalSeries ℂ n χ') (unitaryCompact ℂ n)) (h0 : h ≠ 0) :
    ∃ f : kFiniteFunctions (principalSeries ℂ n χ) (unitaryCompact ℂ n),
      ∫ k : unitaryCompact ℂ n,
          (f : Langlands.GeneralLinear n ℂ → ℂ) k * (h : Langlands.GeneralLinear n ℂ → ℂ) k
            ∂unitaryHaar n ≠ 0 := by
  have hmem := Submodule.mem_inf.mp h.2
  refine ⟨⟨partner s h, Submodule.mem_inf.mpr
    ⟨partner_mem_principalSeries hχ hs hmem.1, partner_mem_kFiniteVectors s hmem.2⟩⟩, ?_⟩
  have heq : (fun k : unitaryCompact ℂ n =>
      partner s (h : Langlands.GeneralLinear n ℂ → ℂ) k *
        (h : Langlands.GeneralLinear n ℂ → ℂ) k) =
      fun k : unitaryCompact ℂ n =>
        ((Complex.normSq ((h : Langlands.GeneralLinear n ℂ → ℂ)
          (k : Langlands.GeneralLinear n ℂ)) : ℝ) : ℂ) := by
    funext k
    rw [partner, gramWeight_unitary s k.2, Complex.ofReal_one, one_mul,
      Complex.normSq_eq_conj_mul_self]
    rfl
  change ∫ k : unitaryCompact ℂ n, partner s (h : Langlands.GeneralLinear n ℂ → ℂ) k *
    (h : Langlands.GeneralLinear n ℂ → ℂ) k ∂unitaryHaar n ≠ 0
  rw [heq, integral_complex_ofReal]
  obtain ⟨k, hk⟩ : ∃ k : unitaryCompact ℂ n, (h : Langlands.GeneralLinear n ℂ → ℂ) k ≠ 0 := by
    by_contra hc
    push Not at hc
    apply h0
    exact (Submodule.coe_eq_zero).mp
      (eq_zero_of_mem_principalSeries_of_eqOn hmem.1 fun k hk => hc ⟨k, hk⟩)
  have hcont : Continuous (h : Langlands.GeneralLinear n ℂ → ℂ) := hmem.1.1.continuous
  have hpos := integral_unitaryHaar_pos
    (f := fun k : unitaryCompact ℂ n => Complex.normSq ((h : Langlands.GeneralLinear n ℂ → ℂ) k))
    (Complex.continuous_normSq.comp (hcont.comp continuous_subtype_val))
    (fun k => Complex.normSq_nonneg _) (k := k) (Complex.normSq_pos.mpr hk).ne'
  exact_mod_cast hpos.ne'

/-! ## Complex position characters -/

/-- The norm of a complex position character is a real power of the norm. -/
theorem exists_normSq_complexPositionCharacter (ds : List ComplexCharacterData) :
    ∃ s : ℕ → ℝ, ∀ i (z : ℂˣ),
      Complex.normSq (complexPositionCharacter ds i z) = Complex.normSq (z : ℂ) ^ s i := by
  induction ds with
  | nil =>
    refine ⟨fun _ => 0, fun i z => ?_⟩
    simp [complexPositionCharacter]
  | cons d ds ih =>
    obtain ⟨s, hs⟩ := ih
    refine ⟨fun i => Nat.casesOn i (2 * d.exponent.re) s, fun i z => ?_⟩
    cases i with
    | succ i => exact hs i z
    | zero =>
      change Complex.normSq (d.character z : ℂ) = Complex.normSq (z : ℂ) ^ (2 * d.exponent.re)
      have hz : 0 < ‖(z : ℂ)‖ := norm_pos_iff.mpr z.ne_zero
      have hnorm : ‖(d.character z : ℂ)‖ = ‖(z : ℂ)‖ ^ (2 * d.exponent.re) := by
        rw [d.character_eq, norm_mul, norm_zpow, norm_div, Complex.norm_real, norm_norm,
          div_self hz.ne', one_zpow, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hz]
        congr 1
        simp
      rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hnorm,
        ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hz.le,
        ← Real.rpow_mul hz.le]
      congr 1
      push_cast
      ring

end Langlands.Archimedean.ComplexDuality
