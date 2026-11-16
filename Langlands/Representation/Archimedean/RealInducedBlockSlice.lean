import Langlands.Representation.Archimedean.RealInducedBlockContour
import Langlands.Representation.Archimedean.RealBlockFourierFinite
import Langlands.Representation.Archimedean.RealBlockLeftDerivative

/-!
# Rotations of upper triangular blocks in `GL_N(ℝ)`

For a block of coordinates `p, p + 1` of `GL_N(ℝ)` let `b(x, y, w)` be the upper triangular
matrix which is the identity outside the block and equals `[[e^x, w], [0, e^y]]` on it.
Left multiplication by a rotation `r_p(θ)` moves `b(x, y, w)` into Iwasawa form:
`r_p(θ) b(x, y, w) = b(x + y - log ρ, log ρ, β₁₂) r_p(arg Z)`, where
`Z(θ) = (e^y cos θ + w sin θ) + i e^x sin θ` is the last row of the block of `r_p(θ) b`
written as a complex number and `ρ = |Z|`.

For a function `F` with `F(b(x, y, w) g) = e^{αx + βy} F(g)` this computes `F(r_p(θ) b g)` in
terms of `F(r_p(φ) g)`. If `φ ↦ F(r_p(φ) g)` is a trigonometric polynomial whose modes `j`
satisfy `|j| ≥ m + 1`, `j ≡ m + 1 (mod 2)`, and `α - β = m + 1`, then the contour bound of
`RealInducedBlockContour` gives
`|Φ_{j₀} F (b(x, y, w) g)| ≤ C · K₀ · e^{(Re α - m/2)(x + y)} / |u|`, `u = ((e^x + e^y) - i w)/2`
(`norm_blockFourierCoefficient_blockB_le`), where `K₀` bounds the coefficients of the
trigonometric polynomial. Since `|Z(θ)| ≤ 2|u|`, the right side is at most a constant times the
average over `θ` of the tied exponential `e^{a x' + (a - 1) y'}`, `a = Re α - m/2`, at the
Iwasawa coordinates of `r_p(θ) b(x, y, w)`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear

set_option backward.isDefEq.respectTransparency false

namespace RealInducedBlockSlice

open RealBlockRotation RealBlockFourierFinite

variable {N p : ℕ}

/-! ## Upper triangular block matrices -/

theorem single_mul_single_self (h : p + 1 < N) :
    Matrix.single (ia h) (ib h) (1 : ℝ) * Matrix.single (ia h) (ib h) 1 = 0 :=
  Matrix.single_mul_single_of_ne _ _ _ _ (ia_ne_ib h).symm _

/-- The upper unipotent matrix `1 + v E_{p,p+1}`. -/
def upperUnit (h : p + 1 < N) (v : ℝ) : Langlands.GeneralLinear N ℝ where
  val := 1 + v • Matrix.single (ia h) (ib h) 1
  inv := 1 - v • Matrix.single (ia h) (ib h) 1
  val_inv := by
    have hE : (v • Matrix.single (ia h) (ib h) (1 : ℝ)) * (v • Matrix.single (ia h) (ib h) 1) =
        0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, single_mul_single_self h, smul_zero, smul_zero]
    simp only [add_mul, mul_sub, one_mul, mul_one, hE]
    abel
  inv_val := by
    have hE : (v • Matrix.single (ia h) (ib h) (1 : ℝ)) * (v • Matrix.single (ia h) (ib h) 1) =
        0 := by
      rw [Matrix.smul_mul, Matrix.mul_smul, single_mul_single_self h, smul_zero, smul_zero]
    simp only [sub_mul, mul_add, one_mul, mul_one, hE]
    abel

theorem upperUnit_apply (h : p + 1 < N) (v : ℝ) (i j : Fin N) :
    (upperUnit h v : Matrix (Fin N) (Fin N) ℝ) i j =
      (if i = j then 1 else 0) + (if i = ia h ∧ j = ib h then v else 0) := by
  change (1 + v • Matrix.single (ia h) (ib h) (1 : ℝ)) i j = _
  rw [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.single_apply]
  congr 1
  by_cases hc : i = ia h ∧ j = ib h
  · rw [ite_eq_left hc, ite_eq_left ⟨hc.1.symm, hc.2.symm⟩, smul_eq_mul, mul_one]
  · rw [ite_eq_right hc, ite_eq_right (fun e => hc ⟨e.1.symm, e.2.symm⟩), smul_zero]

theorem upperUnit_mem (h : p + 1 < N) (v : ℝ) :
    upperUnit h v ∈ upperUnipotent N ℝ := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [upperUnit_apply]
    have hne : i ≠ j := fun e => (lt_irrefl _ (e ▸ hij))
    rw [ite_eq_right hne, zero_add]
    rw [ite_eq_right_iff]
    rintro ⟨rfl, rfl⟩
    exfalso
    have : (ib h : ℕ) < (ia h : ℕ) := hij
    simp [ia, ib] at this
  · change (upperUnit h v : Matrix (Fin N) (Fin N) ℝ) i i = 1
    rw [upperUnit_apply, ite_eq_left rfl, ite_eq_right_iff.mpr, add_zero]
    rintro ⟨rfl, e⟩
    exact absurd e (ia_ne_ib h)

/-- The vector `(…, 0, x, y, 0, …)` with `x, y` in the coordinates `p, p + 1`. -/
def diagVec (h : p + 1 < N) (x y : ℝ) : Fin N → ℝ :=
  fun i => if i = ia h then x else if i = ib h then y else 0

theorem sum_mul_diagVec (h : p + 1 < N) (α : Fin N → ℂ) (x y : ℝ) :
    ∑ i, α i * (diagVec h x y i : ℂ) = α (ia h) * x + α (ib h) * y := by
  have hne := ia_ne_ib h
  rw [Fintype.sum_eq_add (ia h) (ib h) hne]
  · simp [diagVec, hne.symm]
  · rintro i ⟨h1, h2⟩
    simp [diagVec, h1, h2]

/-- The block matrix `b(x, y, w)`: the identity outside the block `p, p + 1` and
`[[e^x, w], [0, e^y]]` on it, as `exp(diag(x, y)) (1 + w e^{-x} E_{p,p+1})`. -/
def blockB (h : p + 1 < N) (x y w : ℝ) : Langlands.GeneralLinear N ℝ :=
  matrixExpUnit N (Matrix.diagonal (diagVec h x y)) * upperUnit h (w * Real.exp (-x))

/-- The diagonal entries `e^x, e^y` of `b(x, y, w)` on the block and `1` elsewhere. -/
def diagEntry (h : p + 1 < N) (x y : ℝ) (i : Fin N) : ℝ :=
  Real.exp (diagVec h x y i)

theorem blockB_apply (h : p + 1 < N) (x y w : ℝ) (i j : Fin N) :
    (blockB h x y w : Matrix (Fin N) (Fin N) ℝ) i j =
      (if i = j then diagEntry h x y i else 0) + (if i = ia h ∧ j = ib h then w else 0) := by
  rw [blockB, Units.val_mul, RealPrincipalSeriesDuality.matrixExpUnit_diagonal,
    Iwasawa.diagonalUnits_val, Matrix.diagonal_mul, upperUnit_apply, mul_add]
  congr 1
  · simp only [Units.val_mk0, diagEntry, mul_ite, mul_one, mul_zero]
  · simp only [Units.val_mk0, mul_ite, mul_zero]
    split_ifs with hij
    · rw [hij.1, diagVec, ite_eq_left rfl, mul_comm, mul_assoc, ← Real.exp_add, neg_add_cancel,
        Real.exp_zero, mul_one]
    · rfl

/-! ## Covariance along the block -/

/-- `F(b(x, y, w) g) = e^{αx + βy} F(g)`. -/
def IsBlockCovariant (h : p + 1 < N) (α β : ℂ) (F : Langlands.GeneralLinear N ℝ → ℂ) : Prop :=
  ∀ (x y w : ℝ) (g : Langlands.GeneralLinear N ℝ),
    F (blockB h x y w * g) = Complex.exp (α * x + β * y) * F g

theorem isBlockCovariant_of_isExpEquivariant (h : p + 1 < N) {α : Fin N → ℂ}
    {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : RealBlockDerivative.IsExpEquivariant α F) :
    IsBlockCovariant h (α (ia h)) (α (ib h)) F := by
  intro x y w g
  have := hF (diagVec h x y) ⟨upperUnit h (w * Real.exp (-x)), upperUnit_mem h _⟩ g
  rw [sum_mul_diagVec] at this
  rw [blockB, this]


/-! ## Matrices supported on the block -/

/-- The matrix which is `[[a, b], [c, d]]` on the block `p, p + 1` and the identity elsewhere. -/
def blockMat (h : p + 1 < N) (a b c d : ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun i j =>
    if i = ia h then (if j = ia h then a else if j = ib h then b else 0)
    else if i = ib h then (if j = ia h then c else if j = ib h then d else 0)
    else if i = j then 1 else 0

theorem blockMat_mul (h : p + 1 < N) (a b c d a' b' c' d' : ℝ) :
    blockMat h a b c d * blockMat h a' b' c' d' =
      blockMat h (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  have hne := ia_ne_ib h
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i = ia h
  · rw [Fintype.sum_eq_add (ia h) (ib h) hne]
    · simp only [blockMat, Matrix.of_apply, hi, hne.symm, ite_true, ite_false]
      split_ifs <;> ring
    · rintro k ⟨hk1, hk2⟩
      simp [blockMat, hi, hk1, hk2]
  · by_cases hi' : i = ib h
    · rw [Fintype.sum_eq_add (ia h) (ib h) hne]
      · simp only [blockMat, Matrix.of_apply, hi', hne.symm, ite_true, ite_false]
        split_ifs <;> ring
      · rintro k ⟨hk1, hk2⟩
        simp [blockMat, hi', hk1, hk2, hne.symm]
    · have hrow : ∀ k, blockMat h a b c d i k = if i = k then 1 else 0 := by
        intro k
        simp only [blockMat, Matrix.of_apply, hi, hi', ite_false]
      simp_rw [hrow, ite_mul, one_mul, zero_mul]
      rw [Finset.sum_ite_eq, ite_eq_left (Finset.mem_univ _)]
      simp only [blockMat, Matrix.of_apply, hi, hi', ite_false]

theorem blockRotation_eq_blockMat (h : p + 1 < N) (θ : ℝ) :
    (blockRotation N p θ : Matrix (Fin N) (Fin N) ℝ) =
      blockMat h (Real.cos θ) (-Real.sin θ) (Real.sin θ) (Real.cos θ) := by
  ext i j
  rw [blockRotation_apply h]
  simp only [blockMat, Matrix.of_apply, ia, ib, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem blockB_eq_blockMat (h : p + 1 < N) (x y w : ℝ) :
    (blockB h x y w : Matrix (Fin N) (Fin N) ℝ) =
      blockMat h (Real.exp x) w 0 (Real.exp y) := by
  ext i j
  rw [blockB_apply]
  simp only [blockMat, Matrix.of_apply, diagEntry, diagVec, ia, ib, Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp

/-! ## Rotations of the block matrices -/

/-- `Z(θ) = (e^y cos θ + w sin θ) + i e^x sin θ`, the last row of the block of `r_p(θ) b(x, y, w)`
read as a complex number. -/
def rotZ (x y w θ : ℝ) : ℂ :=
  ((Real.exp y * Real.cos θ + w * Real.sin θ : ℝ) : ℂ) +
    ((Real.exp x * Real.sin θ : ℝ) : ℂ) * Complex.I

theorem rotZ_re (x y w θ : ℝ) : (rotZ x y w θ).re = Real.exp y * Real.cos θ + w * Real.sin θ := by
  simp only [rotZ, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

theorem rotZ_im (x y w θ : ℝ) : (rotZ x y w θ).im = Real.exp x * Real.sin θ := by
  simp only [rotZ, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_im]
  ring

theorem rotZ_ne_zero (x y w θ : ℝ) : rotZ x y w θ ≠ 0 := by
  intro hZ
  have h1 := congrArg Complex.re hZ
  have h2 := congrArg Complex.im hZ
  rw [rotZ_re, Complex.zero_re] at h1
  rw [rotZ_im, Complex.zero_im] at h2
  have hs : Real.sin θ = 0 := (mul_eq_zero.mp h2).resolve_left (Real.exp_pos x).ne'
  rw [hs, mul_zero, add_zero] at h1
  have hc : Real.cos θ = 0 := (mul_eq_zero.mp h1).resolve_left (Real.exp_pos y).ne'
  have := Real.sin_sq_add_cos_sq θ
  rw [hs, hc] at this
  norm_num at this

/-- The upper right entry `β₁₂` of the upper triangular factor of `r_p(θ) b(x, y, w)`. -/
def rotW (x y w θ : ℝ) : ℝ :=
  Real.cos θ * Real.exp x * ((rotZ x y w θ).im / ‖rotZ x y w θ‖) +
    (Real.cos θ * w - Real.sin θ * Real.exp y) * ((rotZ x y w θ).re / ‖rotZ x y w θ‖)

/-- The Iwasawa decomposition of `r_p(θ) b(x, y, w)`:
`r_p(θ) b(x, y, w) = b(x + y - log ρ, log ρ, β₁₂) r_p(arg Z)` with `ρ = |Z|`. -/
theorem blockRotation_mul_blockB (h : p + 1 < N) (x y w θ : ℝ) :
    blockRotation N p θ * blockB h x y w =
      blockB h (x + y - Real.log ‖rotZ x y w θ‖) (Real.log ‖rotZ x y w θ‖) (rotW x y w θ) *
        blockRotation N p (Complex.arg (rotZ x y w θ)) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, blockRotation_eq_blockMat h, blockRotation_eq_blockMat h,
    blockB_eq_blockMat, blockB_eq_blockMat, blockMat_mul, blockMat_mul]
  have hZ := rotZ_ne_zero x y w θ
  have hρ : 0 < ‖rotZ x y w θ‖ := norm_pos_iff.mpr hZ
  have hsq : ‖rotZ x y w θ‖ ^ 2 =
      (Real.exp y * Real.cos θ + w * Real.sin θ) ^ 2 + (Real.exp x * Real.sin θ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, rotZ_re, rotZ_im]
    ring
  have hcs := Real.sin_sq_add_cos_sq θ
  rw [Complex.cos_arg hZ, Complex.sin_arg, Real.exp_sub, Real.exp_log hρ, Real.exp_add, rotW,
    rotZ_re, rotZ_im]
  set ρ := ‖rotZ x y w θ‖
  congr 1
  · field_simp
    linear_combination (Real.cos θ * Real.exp x) * hsq +
      (Real.exp x * (Real.exp y * Real.cos θ + w * Real.sin θ) * Real.exp y) * hcs
  · field_simp
    linear_combination (Real.cos θ * w - Real.sin θ * Real.exp y) * hsq -
      (Real.exp x * Real.sin θ * Real.exp x * Real.exp y) * hcs
  · field_simp
    ring
  · field_simp
    ring

/-- The rotation formula for block covariant functions. -/
theorem apply_blockRotation_mul_blockB (h : p + 1 < N) {α β : ℂ}
    {F : Langlands.GeneralLinear N ℝ → ℂ} (hF : IsBlockCovariant h α β F) (x y w θ : ℝ)
    (g : Langlands.GeneralLinear N ℝ) :
    F (blockRotation N p θ * (blockB h x y w * g)) =
      Complex.exp (α * ((x + y - Real.log ‖rotZ x y w θ‖ : ℝ) : ℂ) +
        β * ((Real.log ‖rotZ x y w θ‖ : ℝ) : ℂ)) *
        F (blockRotation N p (Complex.arg (rotZ x y w θ)) * g) := by
  rw [← mul_assoc, blockRotation_mul_blockB, mul_assoc, hF]


/-! ## The rotation integrals as contour integrals -/

section Bound

open Complex RealInducedBlockContour

/-- `u = ((e^x + e^y) - i w)/2`, the coefficient of `e^{iθ}` in `Z(θ)`. -/
def waveU (x y w : ℝ) : ℂ :=
  (((Real.exp x + Real.exp y : ℝ) : ℂ) - (w : ℂ) * I) / 2

/-- `w' = ((e^y - e^x) + i w)/2`, the coefficient of `e^{-iθ}` in `Z(θ)`. -/
def waveW (x y w : ℝ) : ℂ :=
  (((Real.exp y - Real.exp x : ℝ) : ℂ) + (w : ℂ) * I) / 2

theorem rotZ_eq_wave (x y w θ : ℝ) : rotZ x y w θ = wave (waveU x y w) (waveW x y w) θ := by
  have e1 : cexp (θ * I) = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have e2 : cexp (-(θ * I)) = (Real.cos θ : ℂ) - (Real.sin θ : ℂ) * I := by
    rw [show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg]
    push_cast
    ring
  rw [rotZ, wave, e1, e2, waveU, waveW]
  simp only [Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub]
  linear_combination ((w : ℂ) * (Real.sin θ : ℂ)) * Complex.I_sq

theorem waveU_re (x y w : ℝ) : (waveU x y w).re = (Real.exp x + Real.exp y) / 2 := by
  simp only [waveU, Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, Complex.ofReal_im]
  ring

theorem le_norm_waveU (x y w : ℝ) : (Real.exp x + Real.exp y) / 2 ≤ ‖waveU x y w‖ := by
  rw [← waveU_re]
  exact Complex.re_le_norm _

theorem norm_waveU_pos (x y w : ℝ) : 0 < ‖waveU x y w‖ :=
  lt_of_lt_of_le (by positivity) (le_norm_waveU x y w)

theorem norm_waveW_lt (x y w : ℝ) : ‖waveW x y w‖ < ‖waveU x y w‖ := by
  have hU : ‖waveU x y w‖ ^ 2 = ((Real.exp x + Real.exp y) ^ 2 + w ^ 2) / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [waveU, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  have hW : ‖waveW x y w‖ ^ 2 = ((Real.exp y - Real.exp x) ^ 2 + w ^ 2) / 4 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [waveW, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
      Complex.I_im]
    ring
  have hlt : ‖waveW x y w‖ ^ 2 < ‖waveU x y w‖ ^ 2 := by
    rw [hU, hW]
    have := mul_pos (Real.exp_pos x) (Real.exp_pos y)
    nlinarith
  exact lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _) hlt

/-- The `j`-th mode `ρ^{-(m+1)} (Z/ρ)^j` of the rotated function, `ρ = |Z|`. -/
def modeTerm (x y w : ℝ) (M : ℕ) (j : ℤ) (θ : ℝ) : ℂ :=
  (((‖rotZ x y w θ‖ : ℝ) : ℂ) ^ (M + 1))⁻¹ * (rotZ x y w θ / ((‖rotZ x y w θ‖ : ℝ) : ℂ)) ^ j

theorem ofReal_norm_ne_zero {Z : ℂ} (hZ : Z ≠ 0) : ((‖Z‖ : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (norm_pos_iff.mpr hZ).ne'

theorem mode_pos {Z : ℂ} (hZ : Z ≠ 0) (M l : ℕ) :
    (((‖Z‖ : ℝ) : ℂ) ^ (M + 1))⁻¹ * (Z / ((‖Z‖ : ℝ) : ℂ)) ^ (((M + 1 + 2 * l : ℕ) : ℤ)) =
      Z ^ l / (starRingEnd ℂ) Z ^ (l + M + 1) := by
  have hρ := ofReal_norm_ne_zero hZ
  have hc : (starRingEnd ℂ) Z ≠ 0 := by rwa [Ne, map_eq_zero]
  have h2 : ((‖Z‖ : ℝ) : ℂ) ^ 2 = Z * (starRingEnd ℂ) Z := (Complex.mul_conj' Z).symm
  have e : ((‖Z‖ : ℝ) : ℂ) ^ (M + 1) * ((‖Z‖ : ℝ) : ℂ) ^ (M + 1 + 2 * l) =
      Z ^ (l + M + 1) * (starRingEnd ℂ) Z ^ (l + M + 1) := by
    rw [← pow_add, ← mul_pow, ← h2, ← pow_mul]
    ring
  rw [zpow_natCast, div_pow, inv_mul_eq_div, div_div, mul_comm (((‖Z‖ : ℝ) : ℂ) ^ _), e,
    div_eq_div_iff (mul_ne_zero (pow_ne_zero _ hZ) (pow_ne_zero _ hc)) (pow_ne_zero _ hc)]
  ring

theorem mode_neg {Z : ℂ} (hZ : Z ≠ 0) (M l : ℕ) :
    (((‖Z‖ : ℝ) : ℂ) ^ (M + 1))⁻¹ * (Z / ((‖Z‖ : ℝ) : ℂ)) ^ (-((M + 1 + 2 * l : ℕ) : ℤ)) =
      (starRingEnd ℂ) Z ^ l / Z ^ (l + M + 1) := by
  have hρ := ofReal_norm_ne_zero hZ
  have h2 : ((‖Z‖ : ℝ) : ℂ) ^ 2 = Z * (starRingEnd ℂ) Z := (Complex.mul_conj' Z).symm
  have e : ((‖Z‖ : ℝ) : ℂ) ^ (M + 1 + 2 * l) =
      ((‖Z‖ : ℝ) : ℂ) ^ (M + 1) * (Z ^ l * (starRingEnd ℂ) Z ^ l) := by
    rw [← mul_pow, ← h2, ← pow_mul, ← pow_add]
  rw [zpow_neg, zpow_natCast, div_pow, inv_div, e]
  field_simp
  ring

theorem expMode_arg {Z : ℂ} (hZ : Z ≠ 0) (j : ℤ) :
    expMode j (Complex.arg Z) = (Z / ((‖Z‖ : ℝ) : ℂ)) ^ j := by
  have h1 : cexp (Complex.arg Z * I) = Z / ((‖Z‖ : ℝ) : ℂ) := by
    rw [eq_div_iff (ofReal_norm_ne_zero hZ), mul_comm]
    exact Complex.norm_mul_exp_arg_mul_I Z
  rw [expMode, mul_assoc, Complex.exp_int_mul, h1]

theorem exp_covariance_factor {α β : ℂ} {M : ℕ} (hαβ : α = β + (M + 1)) (s ρ : ℝ) (hρ : 0 < ρ) :
    cexp (α * ((s - Real.log ρ : ℝ) : ℂ) + β * ((Real.log ρ : ℝ) : ℂ)) =
      cexp (α * s) * (((ρ : ℝ) : ℂ) ^ (M + 1))⁻¹ := by
  have e : α * ((s - Real.log ρ : ℝ) : ℂ) + β * ((Real.log ρ : ℝ) : ℂ) =
      α * s + -(((M + 1 : ℕ) : ℂ) * ((Real.log ρ : ℝ) : ℂ)) := by
    rw [hαβ]
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_neg, Complex.exp_nat_mul, ← Complex.ofReal_exp,
    Real.exp_log hρ]

theorem continuous_rotZ (x y w : ℝ) : Continuous (rotZ x y w) := by
  unfold rotZ
  fun_prop

theorem continuous_modeTerm (x y w : ℝ) (M : ℕ) (j : ℤ) : Continuous (modeTerm x y w M j) := by
  have hc := continuous_rotZ x y w
  have hn : Continuous fun θ => ((‖rotZ x y w θ‖ : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp hc.norm
  have hne : ∀ θ, ((‖rotZ x y w θ‖ : ℝ) : ℂ) ≠ 0 := fun θ =>
    ofReal_norm_ne_zero (rotZ_ne_zero x y w θ)
  exact ((hn.pow _).inv₀ fun θ => pow_ne_zero _ (hne θ)).mul
    ((hc.div hn hne).zpow₀ j fun θ => Or.inl (div_ne_zero (rotZ_ne_zero x y w θ) (hne θ)))

theorem contour_bound_le {u : ℂ} (hu : 0 < ‖u‖) (M l : ℕ) (N : ℤ) :
    2 * Real.pi * (1 / 2 : ℝ) ^ (((l + M + 1 : ℕ) : ℤ) - l + N) *
        (((5 / 4) * ‖u‖) ^ l / ((3 / 4) * ‖u‖) ^ (l + M + 1)) ≤
      2 * Real.pi * (2 ^ N.natAbs * 2 ^ l * 2 ^ (l + M + 1)) / ‖u‖ ^ (M + 1) := by
  have hN : -N ≤ |N| := neg_le_abs N
  have h1 : (1 / 2 : ℝ) ^ (((l + M + 1 : ℕ) : ℤ) - l + N) ≤ 2 ^ N.natAbs := by
    rw [one_div, inv_zpow', ← zpow_natCast]
    exact zpow_le_zpow_right₀ one_le_two (by push_cast; omega)
  have h2 : ((5 / 4) * ‖u‖) ^ l / ((3 / 4) * ‖u‖) ^ (l + M + 1) =
      (5 / 4 : ℝ) ^ l / (3 / 4 : ℝ) ^ (l + M + 1) / ‖u‖ ^ (M + 1) := by
    rw [mul_pow, mul_pow]
    field_simp
    ring
  have h3 : (5 / 4 : ℝ) ^ l / (3 / 4 : ℝ) ^ (l + M + 1) ≤ 2 ^ l * 2 ^ (l + M + 1) := by
    rw [div_le_iff₀ (by positivity), mul_assoc, ← mul_pow]
    norm_num
    calc (5 / 4 : ℝ) ^ l ≤ 2 ^ l := pow_le_pow_left₀ (by norm_num) (by norm_num) l
      _ ≤ 2 ^ l * (3 / 2) ^ (l + M + 1) :=
        le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  rw [h2]
  calc 2 * Real.pi * (1 / 2 : ℝ) ^ (((l + M + 1 : ℕ) : ℤ) - l + N) *
        ((5 / 4 : ℝ) ^ l / (3 / 4 : ℝ) ^ (l + M + 1) / ‖u‖ ^ (M + 1)) ≤
      2 * Real.pi * 2 ^ N.natAbs * (2 ^ l * 2 ^ (l + M + 1) / ‖u‖ ^ (M + 1)) := by
        gcongr
    _ = 2 * Real.pi * (2 ^ N.natAbs * 2 ^ l * 2 ^ (l + M + 1)) / ‖u‖ ^ (M + 1) := by ring

/-- The rotation integral of one mode. -/
theorem norm_integral_modeTerm_le (x y w : ℝ) (M : ℕ) (j0 j : ℤ) (l : ℕ)
    (hj : j = ((M + 1 + 2 * l : ℕ) : ℤ) ∨ j = -((M + 1 + 2 * l : ℕ) : ℤ)) :
    ‖∫ θ in (0 : ℝ)..2 * Real.pi, modeTerm x y w M j θ * cexp (-((j0 : ℂ) * (θ : ℂ) * I))‖ ≤
      2 * Real.pi * (2 ^ j0.natAbs * 2 ^ l * 2 ^ (l + M + 1)) / ‖waveU x y w‖ ^ (M + 1) := by
  have hwu := norm_waveW_lt x y w
  have hu := norm_waveU_pos x y w
  rcases hj with rfl | rfl
  · have hpt : ∀ θ : ℝ, modeTerm x y w M ((M + 1 + 2 * l : ℕ) : ℤ) θ *
        cexp (-((j0 : ℂ) * (θ : ℂ) * I)) =
        wave (waveU x y w) (waveW x y w) θ ^ l /
          ((starRingEnd ℂ) (wave (waveU x y w) (waveW x y w) θ)) ^ (l + M + 1) *
          cexp (((-j0 : ℤ) : ℂ) * θ * I) := by
      intro θ
      rw [modeTerm, mode_pos (rotZ_ne_zero x y w θ), rotZ_eq_wave]
      push_cast
      ring_nf
    simp_rw [hpt]
    refine (norm_integral_le hwu l (l + M + 1) (-j0)).trans ?_
    have := contour_bound_le hu M l (-j0)
    rwa [Int.natAbs_neg] at this
  · have hpt : ∀ θ : ℝ, modeTerm x y w M (-((M + 1 + 2 * l : ℕ) : ℤ)) θ *
        cexp (-((j0 : ℂ) * (θ : ℂ) * I)) =
        (starRingEnd ℂ) (wave (waveU x y w) (waveW x y w) θ ^ l /
          ((starRingEnd ℂ) (wave (waveU x y w) (waveW x y w) θ)) ^ (l + M + 1) *
          cexp ((j0 : ℂ) * θ * I)) := by
      intro θ
      rw [modeTerm, mode_neg (rotZ_ne_zero x y w θ), rotZ_eq_wave, map_mul, map_div₀, map_pow,
        map_pow, Complex.conj_conj, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_ofReal,
        map_intCast, Complex.conj_I]
      ring_nf
    simp_rw [hpt]
    rw [intervalIntegral.intervalIntegral_conj, Complex.norm_conj]
    exact (norm_integral_le hwu l (l + M + 1) j0).trans (contour_bound_le hu M l j0)

theorem norm_waveU_sq (x y w : ℝ) :
    ‖waveU x y w‖ ^ 2 = ((Real.exp x + Real.exp y) ^ 2 + w ^ 2) / 4 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [waveU, Complex.div_ofNat_re, Complex.div_ofNat_im, Complex.sub_re, Complex.sub_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  ring

/-- `e^{(x+y)/2} ≤ |u|`: indeed `|u|² - |w'|² = e^{x+y}`. -/
theorem exp_half_le_norm_waveU (x y w : ℝ) : Real.exp ((x + y) / 2) ≤ ‖waveU x y w‖ := by
  have h2 : Real.exp ((x + y) / 2) ^ 2 = Real.exp x * Real.exp y := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  refine (pow_le_pow_iff_left₀ (Real.exp_pos _).le (norm_nonneg _) two_ne_zero).mp ?_
  rw [h2, norm_waveU_sq]
  nlinarith [sq_nonneg (Real.exp x - Real.exp y), sq_nonneg w]

theorem exp_div_norm_waveU_le (a x y w : ℝ) (M : ℕ) :
    Real.exp (a * (x + y)) / ‖waveU x y w‖ ^ (M + 1) ≤
      Real.exp ((a - M / 2) * (x + y)) / ‖waveU x y w‖ := by
  have hu := norm_waveU_pos x y w
  have hM : Real.exp ((M / 2 : ℝ) * (x + y)) ≤ ‖waveU x y w‖ ^ M := by
    calc Real.exp ((M / 2 : ℝ) * (x + y)) = Real.exp ((x + y) / 2) ^ M := by
          rw [← Real.exp_nat_mul]
          congr 1
          ring
      _ ≤ ‖waveU x y w‖ ^ M :=
          pow_le_pow_left₀ (Real.exp_pos _).le (exp_half_le_norm_waveU x y w) M
  have e : Real.exp (a * (x + y)) =
      Real.exp ((a - M / 2) * (x + y)) * Real.exp ((M / 2 : ℝ) * (x + y)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [div_le_div_iff₀ (by positivity) hu, pow_succ, e]
  calc Real.exp ((a - M / 2) * (x + y)) * Real.exp ((M / 2 : ℝ) * (x + y)) * ‖waveU x y w‖ ≤
        Real.exp ((a - M / 2) * (x + y)) * ‖waveU x y w‖ ^ M * ‖waveU x y w‖ := by gcongr
    _ = Real.exp ((a - M / 2) * (x + y)) * (‖waveU x y w‖ ^ M * ‖waveU x y w‖) := by ring


/-- **The one-block bound.** Let `F` be block covariant with exponents `α, β`, `α - β = m + 1`,
and suppose that `φ ↦ F(r_p(φ) g)` is the trigonometric polynomial
`(2π)⁻¹ Σ_{j ∈ S} c_j e^{ijφ}` whose modes `j` with `c_j ≠ 0` satisfy `|j| ≥ m + 1`,
`j ≡ m + 1 (mod 2)` and `|j| ≤ D`. Then every block Fourier coefficient of `F` at
`b(x, y, w) g` is bounded by `2^{|j₀| + 2D} (Σ |c_j|) e^{(Re α - m/2)(x + y)} / |u|`, where
`u = ((e^x + e^y) - i w)/2` (`waveU`). -/
theorem norm_blockFourierCoefficient_blockB_le (h : p + 1 < N) {α β : ℂ} {M D : ℕ}
    (hαβ : α = β + (M + 1)) {F : Langlands.GeneralLinear N ℝ → ℂ}
    (hF : IsBlockCovariant h α β F) (g : Langlands.GeneralLinear N ℝ) (S : Finset ℤ)
    (c : ℤ → ℂ)
    (hexp : ∀ φ : ℝ, F (blockRotation N p φ * g) =
      (2 * (Real.pi : ℂ))⁻¹ * ∑ j ∈ S, c j * expMode j φ)
    (hD : ∀ j ∈ S, |j| ≤ D)
    (hmode : ∀ j ∈ S, c j ≠ 0 → ∃ l : ℕ,
      j = ((M + 1 + 2 * l : ℕ) : ℤ) ∨ j = -((M + 1 + 2 * l : ℕ) : ℤ))
    (j0 : ℤ) (x y w : ℝ) :
    ‖blockFourierCoefficient N p j0 F (blockB h x y w * g)‖ ≤
      2 ^ (j0.natAbs + 2 * D) * (∑ j ∈ S, ‖c j‖) *
        (Real.exp ((α.re - M / 2) * (x + y)) / ‖waveU x y w‖) := by
  set K : ℤ → ℂ := fun j => cexp (α * ((x + y : ℝ) : ℂ)) * (2 * (Real.pi : ℂ))⁻¹ * c j
  set I0 : ℤ → ℂ := fun j => ∫ θ in (0 : ℝ)..2 * Real.pi,
    modeTerm x y w M j θ * cexp (-((j0 : ℂ) * (θ : ℂ) * I))
  have hpt : ∀ θ : ℝ, F (blockRotation N p θ * (blockB h x y w * g)) *
      cexp (-((j0 : ℂ) * (θ : ℂ) * I)) =
      ∑ j ∈ S, K j * (modeTerm x y w M j θ * cexp (-((j0 : ℂ) * (θ : ℂ) * I))) := by
    intro θ
    have hρ : 0 < ‖rotZ x y w θ‖ := norm_pos_iff.mpr (rotZ_ne_zero x y w θ)
    rw [apply_blockRotation_mul_blockB h hF, hexp, exp_covariance_factor hαβ _ _ hρ,
      Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [expMode_arg (rotZ_ne_zero x y w θ), modeTerm]
    simp only [K]
    ring
  have hrw : blockFourierCoefficient N p j0 F (blockB h x y w * g) = ∑ j ∈ S, K j * I0 j := by
    unfold blockFourierCoefficient
    simp_rw [hpt]
    rw [intervalIntegral.integral_finsetSum fun j _ => ?_]
    · simp only [I0, intervalIntegral.integral_const_mul]
    · have := continuous_modeTerm x y w M j
      exact Continuous.intervalIntegrable (by fun_prop) _ _
  set B : ℝ := 2 ^ (j0.natAbs + 2 * D) *
    (Real.exp (α.re * (x + y)) / ‖waveU x y w‖ ^ (M + 1))
  have hterm : ∀ j ∈ S, ‖K j * I0 j‖ ≤ ‖c j‖ * B := by
    intro j hj
    by_cases hcj : c j = 0
    · simp [K, hcj]
    obtain ⟨l, hl⟩ := hmode j hj hcj
    have hlD : l + M + 1 ≤ D := by
      have := abs_le.mp (hD j hj)
      rcases hl with rfl | rfl <;> push_cast at this <;> omega
    have hI := norm_integral_modeTerm_le x y w M j0 j l hl
    have hK : ‖K j‖ = Real.exp (α.re * (x + y)) * (2 * Real.pi)⁻¹ * ‖c j‖ := by
      simp only [K, norm_mul, Complex.norm_exp, norm_inv]
      rw [Complex.re_mul_ofReal]
      simp [abs_of_pos Real.pi_pos]
    have h22 : (2 : ℝ) ^ l * 2 ^ (l + M + 1) ≤ 2 ^ D * 2 ^ D :=
      mul_le_mul (pow_le_pow_right₀ one_le_two (by omega))
        (pow_le_pow_right₀ one_le_two hlD) (by positivity) (by positivity)
    rw [norm_mul, hK]
    have hu := norm_waveU_pos x y w
    have hI' : ‖I0 j‖ ≤
        2 * Real.pi * (2 ^ j0.natAbs * (2 ^ D * 2 ^ D)) / ‖waveU x y w‖ ^ (M + 1) := by
      have : 2 * Real.pi * (2 ^ j0.natAbs * 2 ^ l * 2 ^ (l + M + 1)) ≤
          2 * Real.pi * (2 ^ j0.natAbs * (2 ^ D * 2 ^ D)) := by
        rw [mul_assoc (2 ^ j0.natAbs : ℝ)]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h22 (by positivity))
          (by positivity)
      exact hI.trans (div_le_div_of_nonneg_right this (by positivity))
    calc Real.exp (α.re * (x + y)) * (2 * Real.pi)⁻¹ * ‖c j‖ * ‖I0 j‖ ≤
        Real.exp (α.re * (x + y)) * (2 * Real.pi)⁻¹ * ‖c j‖ *
          (2 * Real.pi * (2 ^ j0.natAbs * (2 ^ D * 2 ^ D)) / ‖waveU x y w‖ ^ (M + 1)) :=
          mul_le_mul_of_nonneg_left hI' (by positivity)
      _ = ‖c j‖ * B := by
          simp only [B]
          rw [show (2 : ℝ) ^ (j0.natAbs + 2 * D) = 2 ^ j0.natAbs * (2 ^ D * 2 ^ D) by ring]
          field_simp
  rw [hrw]
  have hB : B ≤ 2 ^ (j0.natAbs + 2 * D) *
      (Real.exp ((α.re - M / 2) * (x + y)) / ‖waveU x y w‖) := by
    simp only [B]
    exact mul_le_mul_of_nonneg_left (exp_div_norm_waveU_le α.re x y w M) (by positivity)
  calc ‖∑ j ∈ S, K j * I0 j‖ ≤ ∑ j ∈ S, ‖K j * I0 j‖ := norm_sum_le _ _
    _ ≤ ∑ j ∈ S, ‖c j‖ * B := Finset.sum_le_sum hterm
    _ = (∑ j ∈ S, ‖c j‖) * B := by rw [Finset.sum_mul]
    _ ≤ (∑ j ∈ S, ‖c j‖) * (2 ^ (j0.natAbs + 2 * D) *
          (Real.exp ((α.re - M / 2) * (x + y)) / ‖waveU x y w‖)) := by
        gcongr
    _ = _ := by ring

end Bound

end RealInducedBlockSlice

end Langlands.Archimedean
