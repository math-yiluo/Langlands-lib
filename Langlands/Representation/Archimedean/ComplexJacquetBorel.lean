import Langlands.Representation.Archimedean.StandardModule
import Langlands.Representation.IntegerLattice.GeneralizedWeightGlobalBasisProof
import Langlands.Group.GL.UpperBruhatCoordinatesProof
import Langlands.Representation.Archimedean.ComplexStandardNontrivialProof
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Characters of the upper triangular Borel subgroup of `GL_n(ℂ)`

For integers `l_j` and complex numbers `α_j`, the Borel character is
`β ↦ ∏ⱼ (β_jj/‖β_jj‖)^{l_j} ‖β_jj‖^{α_j}` on matrices `β` with nonzero diagonal
(`borelChar`). It is multiplicative on upper triangular matrices (`borelChar_mul`) and smooth
near matrices with nonzero diagonal (`contDiffAt_borelChar`).

For complex characters `d 0, …, d (n-1)` with weights `l_j` and exponents `t_j`, the character
of the principal series of `d` on `diag(a)` is the Borel character with
`α_j = 2 t_j + (n - 1) - 2 j` at `diag(a)` (`principalSeriesCharacter_ofFn`). Conversely,
`characterOfParams l t` is the complex character `z ↦ (z/‖z‖)^l ‖z‖^{2t}` with weight `l` and
exponent `t`.
-/

noncomputable section

open scoped Matrix ContDiff Matrix.Norms.Operator

set_option autoImplicit false

namespace Langlands.Archimedean

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

/-! ## The factor `z ↦ (z/‖z‖)^l ‖z‖^α` -/

/-- `(z/‖z‖)^l ‖z‖^α`, with `‖z‖^α = exp(α log ‖z‖)`. -/
def borelFactor (l : ℤ) (α : ℂ) (z : ℂ) : ℂ :=
  (z / (‖z‖ : ℂ)) ^ l * Complex.exp ((Real.log ‖z‖ : ℂ) * α)

theorem borelFactor_eq_cpow (l : ℤ) (α : ℂ) {z : ℂ} (hz : z ≠ 0) :
    borelFactor l α z = (z / (‖z‖ : ℂ)) ^ l * (‖z‖ : ℂ) ^ α := by
  have hr : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  rw [borelFactor, Complex.cpow_def_of_ne_zero hr, Complex.ofReal_log (norm_nonneg z)]

theorem borelFactor_ne_zero (l : ℤ) (α : ℂ) {z : ℂ} (hz : z ≠ 0) : borelFactor l α z ≠ 0 := by
  have hr : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  exact mul_ne_zero (zpow_ne_zero _ (div_ne_zero hz hr)) (Complex.exp_ne_zero _)

theorem borelFactor_mul (l : ℤ) (α : ℂ) {z w : ℂ} (hz : z ≠ 0) (hw : w ≠ 0) :
    borelFactor l α (z * w) = borelFactor l α z * borelFactor l α w := by
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hw' : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [borelFactor, borelFactor, borelFactor, norm_mul, Real.log_mul hz' hw', Complex.ofReal_mul,
    Complex.ofReal_add, add_mul, Complex.exp_add, mul_div_mul_comm, mul_zpow]
  ring

@[simp]
theorem borelFactor_one (l : ℤ) (α : ℂ) : borelFactor l α 1 = 1 := by
  simp [borelFactor]

theorem borelFactor_of_norm_eq_one (l : ℤ) (α : ℂ) {z : ℂ} (hz : ‖z‖ = 1) :
    borelFactor l α z = z ^ l := by
  simp [borelFactor, hz]

theorem borelFactor_exp (l : ℤ) (α : ℂ) (s : ℝ) :
    borelFactor l α (Real.exp s : ℂ) = Complex.exp (s * α) := by
  have hn : ‖((Real.exp s : ℝ) : ℂ)‖ = Real.exp s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos s)]
  have h0 : ((Real.exp s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos s).ne'
  rw [borelFactor, hn, div_self h0, one_zpow, one_mul, Real.log_exp]

/-- `borelFactor l α` is `C^∞` (over `ℝ`) away from `0`. -/
theorem contDiffAt_borelFactor (l : ℤ) (α : ℂ) {z : ℂ} (hz : z ≠ 0) :
    ContDiffAt ℝ ∞ (borelFactor l α) z := by
  have hn : ContDiffAt ℝ ∞ (fun x : ℂ => ‖x‖) z := contDiffAt_norm ℝ hz
  have hr : ((‖z‖ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hnc : ContDiffAt ℝ ∞ (fun x : ℂ => ((‖x‖ : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z hn
  have hu : ContDiffAt ℝ ∞ (fun x : ℂ => x / (‖x‖ : ℂ)) z := by
    simp only [div_eq_mul_inv]
    exact (contDiffAt_id (𝕜 := ℝ)).mul (hnc.fun_inv hr)
  have hu0 : z / (‖z‖ : ℂ) ≠ 0 := div_ne_zero hz hr
  have hpow : ContDiffAt ℝ ∞ (fun x : ℂ => (x / (‖x‖ : ℂ)) ^ l) z := by
    rcases l with k | k
    · simp only [Int.ofNat_eq_natCast, zpow_natCast]
      exact hu.pow k
    · simp only [zpow_negSucc]
      exact (hu.pow (k + 1)).fun_inv (pow_ne_zero _ hu0)
  have hlog : ContDiffAt ℝ ∞ (fun x : ℂ => Complex.exp ((Real.log ‖x‖ : ℂ) * α)) z :=
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp z
      (hn.log (norm_ne_zero_iff.mpr hz))).mul contDiffAt_const).cexp
  exact hpow.mul hlog

/-! ## The Borel character -/

section Borel

variable {n : ℕ}

/-- The Borel character `β ↦ ∏ⱼ (β_jj/‖β_jj‖)^{l_j} ‖β_jj‖^{α_j}`. -/
def borelChar (l : Fin n → ℤ) (α : Fin n → ℂ) (M : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  ∏ j, borelFactor (l j) (α j) (M j j)

/-- An invertible upper triangular matrix has nonzero diagonal entries. This adapts the Library
lemma `Langlands.GeneralLinear.UpperBruhatCoordinates.diag_ne_zero_of_upper`, stated for an
element of `GL_n`, to a matrix `M` with `IsUnit M`, by applying it to the unit `hu.unit`. -/
theorem diag_ne_zero_of_upper {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsUpperTriangular)
    (hu : IsUnit M) (j : Fin n) : M j j ≠ 0 := by
  have h := Langlands.GeneralLinear.UpperBruhatCoordinates.diag_ne_zero_of_upper hu.unit
    (by rwa [IsUnit.unit_spec]) j
  rwa [IsUnit.unit_spec] at h

theorem borelChar_mul (l : Fin n → ℤ) (α : Fin n → ℂ) {M N : Matrix (Fin n) (Fin n) ℂ}
    (hM : M.IsUpperTriangular) (hN : N.IsUpperTriangular) (hMd : ∀ j, M j j ≠ 0)
    (hNd : ∀ j, N j j ≠ 0) :
    borelChar l α (M * N) = borelChar l α M * borelChar l α N := by
  simp only [borelChar, Langlands.IntegerLattice.GlobalBlockBasis.upper_mul_diag hM hN,
    borelFactor_mul _ _ (hMd _) (hNd _), Finset.prod_mul_distrib]

@[simp]
theorem borelChar_one (l : Fin n → ℤ) (α : Fin n → ℂ) : borelChar l α 1 = 1 := by
  simp [borelChar]

theorem borelChar_ne_zero (l : Fin n → ℤ) (α : Fin n → ℂ) {M : Matrix (Fin n) (Fin n) ℂ}
    (hMd : ∀ j, M j j ≠ 0) : borelChar l α M ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun j _ => borelFactor_ne_zero _ _ (hMd j)

/-- On a matrix whose diagonal entries have norm one, the Borel character is
`∏ⱼ M_jj^{l_j}`. -/
theorem borelChar_of_norm_diag (l : Fin n → ℤ) (α : Fin n → ℂ) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ j, ‖M j j‖ = 1) : borelChar l α M = ∏ j, (M j j) ^ (l j) :=
  Finset.prod_congr rfl fun j _ => borelFactor_of_norm_eq_one _ _ (hM j)

/-- The Borel character is `C^∞` near a matrix with nonzero diagonal entries. -/
theorem contDiffAt_borelChar (l : Fin n → ℤ) (α : Fin n → ℂ) {M : Matrix (Fin n) (Fin n) ℂ}
    (hM : ∀ j, M j j ≠ 0) : ContDiffAt ℝ ∞ (borelChar l α) M := by
  refine contDiffAt_prod fun j _ => ?_
  have hg : ContDiff ℝ ∞ (fun N : Matrix (Fin n) (Fin n) ℂ => N j j) :=
    (LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ j j)).contDiff
  exact (contDiffAt_borelFactor (l j) (α j) (hM j)).comp M hg.contDiffAt

/-- The Borel character of `diag(a) u β` for `u` upper unipotent and `β` upper triangular. -/
theorem borelChar_diagonalUnits_mul (l : Fin n → ℤ) (α : Fin n → ℂ) (a : Fin n → ℂˣ)
    (u : upperUnipotent n ℂ) {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.IsUpperTriangular)
    (hMd : ∀ j, M j j ≠ 0) :
    borelChar l α (((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) * ((u : Langlands.GeneralLinear n ℂ) :
        Matrix (Fin n) (Fin n) ℂ) * M) =
      (∏ j, borelFactor (l j) (α j) (a j)) * borelChar l α M := by
  set D : Matrix (Fin n) (Fin n) ℂ := ((Iwasawa.diagonalUnits a : Langlands.GeneralLinear n ℂ) :
    Matrix (Fin n) (Fin n) ℂ) with hD
  have hDv : D = Matrix.diagonal fun i => (a i : ℂ) := Iwasawa.diagonalUnits_val a
  have hDu : D.IsUpperTriangular := by
    rw [hDv]
    exact Matrix.blockTriangular_diagonal _
  have huu : ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ).IsUpperTriangular :=
    u.2.1
  have hud : ∀ j, ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ) j j = 1 :=
    u.2.2
  have hDud : ∀ j, (D * ((u : Langlands.GeneralLinear n ℂ) : Matrix (Fin n) (Fin n) ℂ)) j j =
      (a j : ℂ) := by
    intro j
    rw [Langlands.IntegerLattice.GlobalBlockBasis.upper_mul_diag hDu huu, hud, mul_one, hDv,
      Matrix.diagonal_apply_eq]
  rw [borelChar_mul l α (hDu.mul huu) hM (fun j => by rw [hDud]; exact (a j).ne_zero) hMd]
  congr 1
  exact Finset.prod_congr rfl fun j _ => by rw [hDud]

end Borel

/-! ## Complex characters and the principal series character -/

/-- `borelFactor l α` is the Library's `unitChar l (α / 2)` (module
`ComplexStandardNontrivialProof`), which writes `‖z‖^α` as `exp(2 (α / 2) log ‖z‖)`. -/
theorem borelFactor_eq_unitChar (l : ℤ) (α : ℂ) (z : ℂ) :
    borelFactor l α z = unitChar l (α / 2) z := by
  rw [borelFactor, unitChar]
  congr 2
  ring

/-- The weight at position `j` of `List.ofFn d` is the weight of `d j`. -/
theorem posWeight_ofFn :
    ∀ {n : ℕ} (d : Fin n → ComplexCharacterData) (j : Fin n),
      posWeight (List.ofFn d) j = (d j).weight
  | 0, _, j => j.elim0
  | n + 1, d, j => by
    rw [List.ofFn_succ]
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      rw [Fin.val_succ]
      exact posWeight_ofFn (fun i => d i.succ) j

/-- The exponent at position `j` of `List.ofFn d` is the exponent of `d j`. -/
theorem posExponent_ofFn :
    ∀ {n : ℕ} (d : Fin n → ComplexCharacterData) (j : Fin n),
      posExponent (List.ofFn d) j = (d j).exponent
  | 0, _, j => j.elim0
  | n + 1, d, j => by
    rw [List.ofFn_succ]
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      rw [Fin.val_succ]
      exact posExponent_ofFn (fun i => d i.succ) j

/-- The principal series character of the characters `d j` at `diag(a)` is the product of the
factors `(a_j/‖a_j‖)^{l_j} ‖a_j‖^{2 t_j + (n - 1) - 2 j}`. This is the Library theorem
`principalSeriesCharacter_eq` (module `ComplexStandardNontrivialProof`) for the list
`List.ofFn d`, rewritten with `borelFactor_eq_unitChar`, `posWeight_ofFn` and
`posExponent_ofFn`. -/
theorem principalSeriesCharacter_ofFn {n : ℕ} (d : Fin n → ComplexCharacterData)
    (a : Fin n → ℂˣ) :
    principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn d)) a =
      ∏ j, borelFactor (d j).weight
        (2 * (d j).exponent + ((n : ℂ) - 1) - 2 * ((j : ℕ) : ℂ)) (a j) := by
  rw [principalSeriesCharacter_eq]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [borelFactor_eq_unitChar, posWeight_ofFn, posExponent_ofFn]
  congr 1
  ring

/-- The complex character `z ↦ (z/‖z‖)^l ‖z‖^{2t}` with weight `l` and exponent `t`. -/
def characterOfParams (l : ℤ) (t : ℂ) : ComplexCharacterData where
  character :=
    { toFun := fun z => Units.mk0 (borelFactor l (2 * t) (z : ℂ))
        (borelFactor_ne_zero l (2 * t) z.ne_zero)
      map_one' := by
        apply Units.ext
        simp
      map_mul' := fun z w => by
        apply Units.ext
        simp only [Units.val_mul, Units.val_mk0]
        exact borelFactor_mul l (2 * t) z.ne_zero w.ne_zero
      continuous_toFun := by
        have hc : Continuous fun z : ℂˣ => borelFactor l (2 * t) (z : ℂ) := by
          rw [continuous_iff_continuousAt]
          intro z
          exact ((contDiffAt_borelFactor l (2 * t) z.ne_zero).continuousAt).comp
            Units.continuous_val.continuousAt
        refine Units.continuous_iff.mpr ⟨hc, ?_⟩
        simp only [Units.val_inv_eq_inv_val, Units.val_mk0]
        exact hc.inv₀ fun z => borelFactor_ne_zero l (2 * t) z.ne_zero }
  weight := l
  exponent := t
  character_eq z := borelFactor_eq_cpow l (2 * t) z.ne_zero

@[simp]
theorem characterOfParams_weight (l : ℤ) (t : ℂ) : (characterOfParams l t).weight = l :=
  rfl

@[simp]
theorem characterOfParams_exponent (l : ℤ) (t : ℂ) : (characterOfParams l t).exponent = t :=
  rfl

/-- The character reconstructed from its weight and exponent is the original character. -/
theorem characterOfParams_eta (d : ComplexCharacterData) :
    characterOfParams d.weight d.exponent = d := by
  cases d with
  | mk χ w t hχ =>
    have he : χ = (characterOfParams w t).character := by
      ext1 z
      apply Units.ext
      change (χ z : ℂ) = borelFactor w (2 * t) (z : ℂ)
      rw [borelFactor_eq_cpow w (2 * t) z.ne_zero]
      exact hχ z
    subst χ
    rfl

end Langlands.Archimedean
