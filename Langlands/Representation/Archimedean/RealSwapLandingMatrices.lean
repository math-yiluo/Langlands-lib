import Langlands.Representation.Archimedean.RealSwapLandingRankOne
import Langlands.Representation.Archimedean.PartialJacquetIntegral
import Langlands.Representation.Archimedean.RealJacquetFrobeniusProof

/-!
# Explicit `GL_3(ℝ)` matrices for the landing integrals

See the companion Markdown file.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set
open scoped Matrix

namespace Langlands.Archimedean

namespace RealSwapLandingMatrices

open RealSwapLandingKernel RealSwapLandingRankOne RealBlockRotation MaximalParabolicIntegration
  PartialJacquet RealJacquetFrobenius Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

/-! ## Elements of `GL_3(ℝ)` from explicit matrices -/

/-- A `3 × 3` matrix with nonzero determinant, as an element of `GL_3(ℝ)`. -/
def glOf (M : Matrix (Fin 3) (Fin 3) ℝ) (h : M.det ≠ 0) : Langlands.GeneralLinear 3 ℝ :=
  ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h)).unit

@[simp]
theorem glOf_val (M : Matrix (Fin 3) (Fin 3) ℝ) (h : M.det ≠ 0) :
    ((glOf M h : Langlands.GeneralLinear 3 ℝ) : Matrix (Fin 3) (Fin 3) ℝ) = M :=
  IsUnit.unit_spec _

/-- `n̄₀(y)`: the lower unipotent matrix with entry `y` at `(1, 0)`. -/
def nbar0 (y : ℝ) : Langlands.GeneralLinear 3 ℝ :=
  glOf !![1, 0, 0; y, 1, 0; 0, 0, 1] (by simp [Matrix.det_fin_three])

/-- `n̄₁(y)`: the lower unipotent matrix with entry `y` at `(2, 1)`. -/
def nbar1 (y : ℝ) : Langlands.GeneralLinear 3 ℝ :=
  glOf !![1, 0, 0; 0, 1, 0; 0, y, 1] (by simp [Matrix.det_fin_three])

/-- `s₀`: the permutation matrix of the transposition `(0 1)`. -/
def s0 : Langlands.GeneralLinear 3 ℝ :=
  glOf !![0, 1, 0; 1, 0, 0; 0, 0, 1] (by simp [Matrix.det_fin_three])

/-- `s₁`: the permutation matrix of the transposition `(1 2)`. -/
def s1 : Langlands.GeneralLinear 3 ℝ :=
  glOf !![1, 0, 0; 0, 0, 1; 0, 1, 0] (by simp [Matrix.det_fin_three])

/-- `w`: the permutation matrix with rows `e₁, e₂, e₀`. -/
def wPerm : Langlands.GeneralLinear 3 ℝ :=
  glOf !![0, 1, 0; 0, 0, 1; 1, 0, 0] (by simp [Matrix.det_fin_three])

/-- The upper triangular matrix with diagonal `(a, b, c)` and entries `x, y, z` above it. -/
def upper3 (a b c : ℝˣ) (x y z : ℝ) : Langlands.GeneralLinear 3 ℝ :=
  glOf !![(a : ℝ), x, y; 0, (b : ℝ), z; 0, 0, (c : ℝ)] (by
    simp [Matrix.det_fin_three, a.ne_zero, b.ne_zero, c.ne_zero])

theorem wPerm_mem_unitaryCompact : wPerm ∈ unitaryCompact ℝ 3 := by
  change ((wPerm : Langlands.GeneralLinear 3 ℝ) : Matrix (Fin 3) (Fin 3) ℝ) ∈
    Matrix.unitaryGroup (Fin 3) ℝ
  rw [Matrix.mem_unitaryGroup_iff, wPerm, glOf_val, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-! ## The rotations and the chart -/

theorem rot0_val (θ : ℝ) : (blockRotation 3 0 θ : Matrix (Fin 3) (Fin 3) ℝ) =
    !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1] := by
  ext i j
  rw [blockRotation_apply (by norm_num) θ i j]
  fin_cases i <;> fin_cases j <;> simp

theorem rot1_val (θ : ℝ) : (blockRotation 3 1 θ : Matrix (Fin 3) (Fin 3) ℝ) =
    !![1, 0, 0; 0, Real.cos θ, -Real.sin θ; 0, Real.sin θ, Real.cos θ] := by
  ext i j
  rw [blockRotation_apply (by norm_num) θ i j]
  fin_cases i <;> fin_cases j <;> simp

theorem chartGL_val (v : Fin 2 → ℝ) : (chartGL v : Matrix (Fin 3) (Fin 3) ℝ) =
    !![1, 0, 0; 0, 1, 0; v 0, v 1, 1] := by
  rw [chartGL, JGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-! ## Matrix identities -/

theorem chartGL_mul_wPerm (v : Fin 2 → ℝ) :
    chartGL v * wPerm = nbar1 (v 1) * s1 * (nbar0 (v 0) * s0) := by
  apply Units.ext
  simp only [Units.val_mul, chartGL_val, wPerm, nbar0, nbar1, s0, s1, glOf_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem wPerm_mul_rot1 (θ : ℝ) :
    wPerm * blockRotation 3 1 θ = blockRotation 3 0 θ * wPerm := by
  apply Units.ext
  simp only [Units.val_mul, rot0_val, rot1_val, wPerm, glOf_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

/-- The inverse rotation `R(-θ)` of the plane, acting on row vectors. -/
def rotInv (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos θ, Real.sin θ; -Real.sin θ, Real.cos θ]

theorem det_rotInv (θ : ℝ) : (rotInv θ).det = 1 := by
  rw [rotInv, Matrix.det_fin_two_of]
  linear_combination Real.sin_sq_add_cos_sq θ

theorem rot0_mul_chartGL (θ : ℝ) (v : Fin 2 → ℝ) :
    blockRotation 3 0 θ * chartGL v = chartGL (v ᵥ* rotInv θ) * blockRotation 3 0 θ := by
  apply Units.ext
  simp only [Units.val_mul, rot0_val, chartGL_val]
  have hs := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, rotInv, Matrix.vecMul, dotProduct,
      Fin.sum_univ_two] <;>
    first
    | linear_combination (v 0) * hs
    | linear_combination (-(v 0)) * hs
    | linear_combination (v 1) * hs
    | linear_combination (-(v 1)) * hs

theorem nbar1_cotan {θ : ℝ} (hS : Real.sin θ ≠ 0) :
    nbar1 (cotan θ) * s1 =
      upper3 1 (Units.mk0 (-Real.sin θ) (neg_ne_zero.mpr hS))
        (Units.mk0 (Real.sin θ)⁻¹ (inv_ne_zero hS)) 0 0 (Real.cos θ) * blockRotation 3 1 θ := by
  apply Units.ext
  simp only [Units.val_mul, rot1_val, nbar1, s1, upper3, glOf_val, Units.val_mk0, Units.val_one]
  have hs := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, cotan, hS] <;>
    first
    | ring1
    | linear_combination hs
    | linear_combination (-1 : ℝ) * hs

theorem nbar0_cotan {θ : ℝ} (hS : Real.sin θ ≠ 0) :
    nbar0 (cotan θ) * s0 =
      upper3 (Units.mk0 (-Real.sin θ) (neg_ne_zero.mpr hS))
        (Units.mk0 (Real.sin θ)⁻¹ (inv_ne_zero hS)) 1 (Real.cos θ) 0 0 * blockRotation 3 0 θ := by
  apply Units.ext
  simp only [Units.val_mul, rot0_val, nbar0, s0, upper3, glOf_val, Units.val_mk0, Units.val_one]
  have hs := Real.sin_sq_add_cos_sq θ
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, cotan, hS] <;>
    first
    | ring1
    | linear_combination hs
    | linear_combination (-1 : ℝ) * hs

theorem nbar1_s1_upper3 {S : ℝ} (hS : S ≠ 0) (C y : ℝ) :
    nbar1 y * s1 * upper3 (Units.mk0 (-S) (neg_ne_zero.mpr hS)) (Units.mk0 S⁻¹ (inv_ne_zero hS)) 1
        C 0 0 =
      upper3 (Units.mk0 (-S) (neg_ne_zero.mpr hS)) 1 (Units.mk0 S⁻¹ (inv_ne_zero hS))
        (-(C * y * S)) C 0 * (nbar1 (y * S) * s1) := by
  apply Units.ext
  simp only [Units.val_mul, nbar1, s1, upper3, glOf_val, Units.val_mk0, Units.val_one]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three] <;>
    first
    | ring1
    | field_simp

/-! ## Upper triangular left translations in the principal series of `GL_3(ℝ)` -/

theorem upper3_blockTriangular (a b c : ℝˣ) (x y z : ℝ) :
    ((upper3 a b c x y z : Langlands.GeneralLinear 3 ℝ) :
      Matrix (Fin 3) (Fin 3) ℝ).BlockTriangular id := by
  intro i j hij
  rw [upper3, glOf_val]
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

theorem mul_upper3 {χ : ℕ → ℝˣ → ℂ} {f : Langlands.GeneralLinear 3 ℝ → ℂ}
    (hf : f ∈ principalSeries ℝ 3 χ) (a b c : ℝˣ) (x y z : ℝ) (g : Langlands.GeneralLinear 3 ℝ) :
    f (upper3 a b c x y z * g) = principalSeriesCharacter ℝ 3 χ ![a, b, c] * f g :=
  mul_of_upperTriangular hf _ (upper3_blockTriangular a b c x y z) _ (fun i => by
    rw [upper3, glOf_val]
    fin_cases i <;> simp) g

/-- The character of the principal series of `GL_3(ℝ)`, written out. -/
theorem principalSeriesCharacter_three (χ : ℕ → ℝˣ → ℂ) (a : Fin 3 → ℝˣ) :
    principalSeriesCharacter ℝ 3 χ a =
      χ 0 (a 0) * ((|(a 0 : ℝ)| : ℝ) : ℂ) * χ 1 (a 1) *
        (χ 2 (a 2) * (((|(a 2 : ℝ)| : ℝ) : ℂ))⁻¹) := by
  unfold principalSeriesCharacter
  rw [Fin.prod_univ_three]
  simp only [Module.finrank_self, pow_one, Real.norm_eq_abs]
  have e0 : (((3 : ℕ) : ℂ) - 1) / 2 - (((0 : Fin 3) : ℕ) : ℂ) = 1 := by norm_num
  have e1 : (((3 : ℕ) : ℂ) - 1) / 2 - (((1 : Fin 3) : ℕ) : ℂ) = 0 := by norm_num
  have e2 : (((3 : ℕ) : ℂ) - 1) / 2 - (((2 : Fin 3) : ℕ) : ℂ) = -1 := by norm_num
  rw [e0, e1, e2, Complex.cpow_one, Complex.cpow_zero, Complex.cpow_neg_one]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  ring

/-! ## The characters of `[induced d, character (charData e s)]` -/

/-- The position characters of the blocks `[induced d, character (charData e s)]`. -/
def posChar (d : ComplexCharacterData) (e : Fin 2) (s : ℂ) : ℕ → ℝˣ → ℂ :=
  realPositionCharacter [RealBlock.induced d, RealBlock.character (charData e s)]

theorem posChar_zero (d : ComplexCharacterData) (e : Fin 2) (s : ℂ) (x : ℝˣ) :
    posChar d e s 0 x = realInducedFirstCharacter d x := rfl

theorem posChar_one (d : ComplexCharacterData) (e : Fin 2) (s : ℂ) (x : ℝˣ) :
    posChar d e s 1 x = realInducedSecondCharacter d x := rfl

theorem posChar_two (d : ComplexCharacterData) (e : Fin 2) (s : ℂ) (x : ℝˣ) :
    posChar d e s 2 x = charFun e s x :=
  charData_character_apply e s x

theorem ofReal_inv_cpow {S : ℝ} (hS : 0 < S) (z : ℂ) :
    ((S⁻¹ : ℝ) : ℂ) ^ z = (S : ℂ) ^ (-z) := by
  rw [Complex.ofReal_inv, Complex.inv_cpow _ _ (by
    rw [Complex.arg_ofReal_of_nonneg hS.le]
    exact Real.pi_ne_zero.symm), Complex.cpow_neg]

theorem charFun_inv {S : ℝ} (hS : 0 < S) (e : Fin 2) (s : ℂ) :
    charFun e s S⁻¹ = (S : ℂ) ^ (-s) := by
  unfold charFun
  rw [abs_of_pos (inv_pos.mpr hS), div_self (inv_pos.mpr hS).ne', Complex.ofReal_one, one_pow,
    one_mul, ofReal_inv_cpow hS]

/-- The character at `diag(1, -S, S⁻¹)`, for the exponent `s = t - ℓ/2 - (n + 1)`. -/
theorem principalSeriesCharacter_block1 (d : ComplexCharacterData) (e : Fin 2) (n : ℕ) {s : ℂ}
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1)) {S : ℝ} (hS : 0 < S) :
    principalSeriesCharacter ℝ 3 (posChar d e s)
        ![1, Units.mk0 (-S) (neg_ne_zero.mpr hS.ne'), Units.mk0 S⁻¹ (inv_ne_zero hS.ne')] =
      ((S ^ (n + 2) : ℝ) : ℂ) := by
  rw [principalSeriesCharacter_three, posChar_zero, posChar_one, posChar_two]
  simp only [Matrix.cons_val, Units.val_one, Units.val_mk0]
  have h0 : realInducedFirstCharacter d 1 = 1 := by
    simp [realInducedFirstCharacter]
  have h1 : realInducedSecondCharacter d (Units.mk0 (-S) (neg_ne_zero.mpr hS.ne')) =
      (S : ℂ) ^ (d.exponent - (d.weight.natAbs : ℂ) / 2) := by
    rw [realInducedSecondCharacter, Units.val_mk0, abs_neg, abs_of_pos hS]
  have hS' : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  rw [h0, h1, abs_one, charFun_inv hS, abs_of_pos (inv_pos.mpr hS), Complex.ofReal_inv, inv_inv,
    Complex.ofReal_one]
  calc (1 : ℂ) * 1 * (S : ℂ) ^ (d.exponent - (d.weight.natAbs : ℂ) / 2) * ((S : ℂ) ^ (-s) * S)
      = (S : ℂ) ^ (d.exponent - (d.weight.natAbs : ℂ) / 2) * (S : ℂ) ^ (-s) *
          (S : ℂ) ^ (1 : ℂ) := by
        rw [Complex.cpow_one]
        ring
    _ = (S : ℂ) ^ ((d.exponent - (d.weight.natAbs : ℂ) / 2) + -s + 1) := by
        rw [← Complex.cpow_add _ _ hS', ← Complex.cpow_add _ _ hS']
    _ = (S : ℂ) ^ (((n + 2 : ℕ)) : ℂ) := by
        congr 1
        rw [hs]
        push_cast
        ring
    _ = ((S ^ (n + 2) : ℝ) : ℂ) := by
        rw [Complex.cpow_natCast, Complex.ofReal_pow]

/-- The character at `diag(-S, 1, S⁻¹)`, for the exponent `s = t - ℓ/2 - (n + 1)`. -/
theorem principalSeriesCharacter_block0 (d : ComplexCharacterData) (e : Fin 2) (n : ℕ) {s : ℂ}
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1)) {S : ℝ} (hS : 0 < S) :
    principalSeriesCharacter ℝ 3 (posChar d e s)
        ![Units.mk0 (-S) (neg_ne_zero.mpr hS.ne'), 1, Units.mk0 S⁻¹ (inv_ne_zero hS.ne')] =
      (-1 : ℂ) ^ (d.weight.natAbs + 1) * ((S ^ (n + d.weight.natAbs + 3) : ℝ) : ℂ) := by
  rw [principalSeriesCharacter_three, posChar_zero, posChar_one, posChar_two]
  simp only [Matrix.cons_val, Units.val_mk0]
  have h0 : realInducedFirstCharacter d (Units.mk0 (-S) (neg_ne_zero.mpr hS.ne')) =
      (-1 : ℂ) ^ (d.weight.natAbs + 1) * (S : ℂ) ^ (d.exponent + (d.weight.natAbs : ℂ) / 2) := by
    rw [realInducedFirstCharacter, Units.val_mk0, abs_neg, abs_of_pos hS, neg_div,
      div_self hS.ne', Complex.ofReal_neg, Complex.ofReal_one]
  have h1 : realInducedSecondCharacter d 1 = 1 := by
    simp [realInducedSecondCharacter]
  have hS' : (S : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  rw [h0, h1, abs_neg, abs_of_pos hS, charFun_inv hS, abs_of_pos (inv_pos.mpr hS),
    Complex.ofReal_inv, inv_inv]
  calc (-1 : ℂ) ^ (d.weight.natAbs + 1) * (S : ℂ) ^ (d.exponent + (d.weight.natAbs : ℂ) / 2) *
        (S : ℂ) * 1 * ((S : ℂ) ^ (-s) * S)
      = (-1 : ℂ) ^ (d.weight.natAbs + 1) * ((S : ℂ) ^ (d.exponent + (d.weight.natAbs : ℂ) / 2) *
          (S : ℂ) ^ (-s) * (S : ℂ) ^ (1 : ℂ) * (S : ℂ) ^ (1 : ℂ)) := by
        rw [Complex.cpow_one]
        ring
    _ = (-1 : ℂ) ^ (d.weight.natAbs + 1) *
          (S : ℂ) ^ ((d.exponent + (d.weight.natAbs : ℂ) / 2) + -s + 1 + 1) := by
        rw [← Complex.cpow_add _ _ hS', ← Complex.cpow_add _ _ hS', ← Complex.cpow_add _ _ hS']
    _ = (-1 : ℂ) ^ (d.weight.natAbs + 1) * (S : ℂ) ^ (((n + d.weight.natAbs + 3 : ℕ)) : ℂ) := by
        congr 2
        rw [hs]
        push_cast
        ring
    _ = _ := by
        rw [Complex.cpow_natCast, Complex.ofReal_pow]

/-! ## The rank-one equivariance of `f` and of `C¹_n f` -/

section RankOne

variable {d : ComplexCharacterData} {e : Fin 2} {n : ℕ} {s : ℂ}
  {f : Langlands.GeneralLinear 3 ℝ → ℂ}

/-- `f(n̄₁(cot θ) s₁ x) = sin^{n+2} θ f(r₁(θ) x)` on `(0, π)`. -/
theorem principalSeries_nbar1_cotan
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1))
    (hf : f ∈ principalSeries ℝ 3 (posChar d e s)) :
    ∀ θ ∈ Ioo 0 Real.pi, ∀ x, f (nbar1 (cotan θ) * s1 * x) =
      1 * ((Real.sin θ ^ (n + 2) : ℝ) : ℂ) * f (blockRotation 3 1 θ * x) := by
  intro θ hθ x
  have hS := sin_pos_of_mem_Ioo hθ
  rw [nbar1_cotan hS.ne', mul_assoc, mul_upper3 hf, one_mul,
    principalSeriesCharacter_block1 d e n hs hS]

/-- `∫_ℝ f(n̄₁(y) s₁ g) dy = C¹_n f(g)` for every `g`. -/
theorem integral_nbar1
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1))
    (hf : f ∈ principalSeries ℝ 3 (posChar d e s)) (g : Langlands.GeneralLinear 3 ℝ) :
    ∫ y, f (nbar1 y * s1 * g) = kernelOp 3 1 n f g := by
  rw [integral_eq_kernelOp 1 n nbar1 s1 1 (principalSeries_nbar1_cotan hs hf) g, one_mul]

/-- `C¹_n f(n̄₀(cot θ) s₀ x) = (-1)^{ℓ+1} sin^{n+ℓ+2} θ C¹_n f(r₀(θ) x)` on `(0, π)`. -/
theorem kernelOp_nbar0_cotan
    (hs : s = d.exponent - (d.weight.natAbs : ℂ) / 2 - ((n : ℂ) + 1))
    (hf : f ∈ principalSeries ℝ 3 (posChar d e s)) :
    ∀ θ ∈ Ioo 0 Real.pi, ∀ x, kernelOp 3 1 n f (nbar0 (cotan θ) * s0 * x) =
      (-1 : ℂ) ^ (d.weight.natAbs + 1) * ((Real.sin θ ^ (n + d.weight.natAbs + 2) : ℝ) : ℂ) *
        kernelOp 3 1 n f (blockRotation 3 0 θ * x) := by
  intro θ hθ x
  have hS := sin_pos_of_mem_Ioo hθ
  rw [nbar0_cotan hS.ne', mul_assoc, ← integral_nbar1 hs hf, ← integral_nbar1 hs hf]
  have he : ∀ y, f (nbar1 y * s1 * (upper3 (Units.mk0 (-Real.sin θ) (neg_ne_zero.mpr hS.ne'))
      (Units.mk0 (Real.sin θ)⁻¹ (inv_ne_zero hS.ne')) 1 (Real.cos θ) 0 0 *
        (blockRotation 3 0 θ * x))) =
      principalSeriesCharacter ℝ 3 (posChar d e s)
        ![Units.mk0 (-Real.sin θ) (neg_ne_zero.mpr hS.ne'), 1,
          Units.mk0 (Real.sin θ)⁻¹ (inv_ne_zero hS.ne')] *
        f (nbar1 (y * Real.sin θ) * s1 * (blockRotation 3 0 θ * x)) := by
    intro y
    rw [← mul_assoc, nbar1_s1_upper3 hS.ne' (Real.cos θ) y, mul_assoc, mul_upper3 hf]
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_mul_right
      (fun y => f (nbar1 y * s1 * (blockRotation 3 0 θ * x))) (Real.sin θ),
    principalSeriesCharacter_block0 d e n hs hS, abs_inv, abs_of_pos hS, Complex.real_smul]
  have key : ((Real.sin θ ^ (n + d.weight.natAbs + 3) : ℝ) : ℂ) * (((Real.sin θ)⁻¹ : ℝ) : ℂ) =
      ((Real.sin θ ^ (n + d.weight.natAbs + 2) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul]
    congr 1
    rw [pow_succ]
    field_simp
  rw [← key]
  ring

end RankOne

end RealSwapLandingMatrices

end Langlands.Archimedean
