import Langlands.Global.RankinSelberg.ComplexLocalEqualQuotientChange
import Langlands.HarmonicAnalysis.FiniteProductMeasureScaling

/-! # The complex equal-rank kernels under a change of additive character -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open GeneralLinear.Iwasawa (diagonalUnits_val diagonalUnits_mul_mul_apply)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "detWeight" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "row" => Langlands.RankinSelberg.lastRow
local notation "diag" => GeneralLinear.Iwasawa.diagonalUnits (F := ℂ)

/-- Powers of the usual absolute value of the additive-character parameter. -/
def amplitude (a : ℂˣ) (s : ℂ) : ℂ :=
  Complex.exp (s * (Real.log ‖(a : ℂ)‖ : ℂ))

theorem amplitude_ne_zero (a : ℂˣ) (s : ℂ) : amplitude a s ≠ 0 :=
  Complex.exp_ne_zero _

theorem amplitude_add (a : ℂˣ) (s t : ℂ) :
    amplitude a (s + t) = amplitude a s * amplitude a t := by
  simp only [amplitude, add_mul, Complex.exp_add]

theorem amplitude_cpow (a : ℂˣ) (s : ℂ) :
    amplitude a s = (‖(a : ℂ)‖ : ℂ) ^ s := by
  have h : (‖(a : ℂ)‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr a.ne_zero
  rw [Complex.cpow_def_of_ne_zero h, amplitude, Complex.ofReal_log (norm_nonneg _), mul_comm]

theorem amplitude_natCast (a : ℂˣ) (k : ℕ) :
    amplitude a (k : ℂ) = (‖(a : ℂ)‖ : ℂ) ^ k := by
  rw [amplitude_cpow, Complex.cpow_natCast]

private theorem detWeight_mul (g h : G) (s : ℂ) :
    detWeight (g * h) s = detWeight g s * detWeight h s := by
  have hd (x : G) : complexNormalizedAbs (Matrix.det x.val) ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (GeneralLinear.determinant x).ne_zero)
  have habs (x y : ℂ) : complexNormalizedAbs (x * y) =
      complexNormalizedAbs x * complexNormalizedAbs y := by
    simp [complexNormalizedAbs, mul_pow]
  simp only [ArchimedeanLocal.detPower, Units.val_mul, Matrix.det_mul, habs,
    Real.log_mul (hd g) (hd h), Complex.ofReal_add, mul_add, Complex.exp_add]

private theorem detWeight_diagonal (a : ℂˣ) (f : Fin (r + 1) → ℕ) (s : ℂ) :
    detWeight (diag fun i => a ^ f i) s =
      amplitude a (((2 * ∑ i, f i : ℕ) : ℂ) * s) := by
  simp only [ArchimedeanLocal.detPower, diagonalUnits_val, Matrix.det_diagonal,
    Units.val_pow_eq_pow_val, Finset.prod_pow_eq_pow_sum, complexNormalizedAbs, norm_pow,
    ← pow_mul, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat, Complex.ofReal_mul, Complex.ofReal_natCast,
    amplitude]
  congr 1
  norm_num
  ring

private theorem twice_sum_diagonal_exponents (r : ℕ) :
    2 * (∑ i : Fin (r + 1), (r - i.val)) = r * (r + 1) := by
  let f : Fin (r + 1) → ℕ := fun i => r - i.val
  have hrev (i : Fin (r + 1)) : f i.rev + f i = r := by
    have hi := i.isLt
    simp only [f, Fin.val_rev]
    omega
  change 2 * (∑ i, f i) = _
  calc
    _ = (∑ i, f (Fin.revPerm i)) + (∑ i, f i) := by
      rw [Equiv.sum_comp, two_mul]
    _ = ∑ i, (f i.rev + f i) := Finset.sum_add_distrib.symm
    _ = _ := by
      simp [hrev, Nat.mul_comm]

private theorem detWeight_changeDiagonal (a : ℂˣ) (s : ℂ) :
    detWeight (changeDiagonal r a) s = amplitude a ((r : ℂ) * (r + 1) * s) := by
  unfold changeDiagonal
  rw [detWeight_diagonal, twice_sum_diagonal_exponents]
  push_cast
  rfl

private theorem diagonal_const (z : ℂˣ) :
    diag (fun _ : Fin (r + 1) => z) = (GeneralLinear.scalar z : G) := rfl

private theorem detWeight_scalar (a : ℂˣ) (s : ℂ) :
    detWeight (GeneralLinear.scalar a : G) s = amplitude a (2 * (r + 1) * s) := by
  have h : (GeneralLinear.scalar a : G) = diag (fun _ => a ^ (1 : ℕ)) := by
    simp only [pow_one, diagonal_const]
  rw [h, detWeight_diagonal]
  simp

private theorem lastRow_shift (a z : ℂˣ) (g : G) (j : Fin (r + 1)) :
    row (changeDiagonal r a * g * GeneralLinear.scalar z) j = (z : ℂ) * row g j := by
  change (changeDiagonal r a * g * (GeneralLinear.scalar z : G)) (Fin.last r) j =
    (z : ℂ) * g (Fin.last r) j
  rw [changeDiagonal, ← diagonal_const, diagonalUnits_mul_mul_apply]
  simp [mul_comm]

private theorem inverseTranspose_diagonal (d : Fin (r + 1) → ℂˣ) :
    GeneralLinear.inverseTranspose (r + 1) ℂ (diag d) = diag d⁻¹ := by
  apply Units.ext
  ext i j
  change GeneralLinear.inverseTranspose (r + 1) ℂ (diag d) i j = (diag d⁻¹) i j
  rw [GeneralLinear.inverseTranspose_entry, ← map_inv]
  simp only [diagonalUnits_val, Matrix.diagonal_apply, eq_comm (a := j) (b := i)]
  split <;> simp_all

private theorem longWeyl_conj_diagonal (d : Fin (r + 1) → ℂˣ) :
    GeneralLinear.weylLong (r + 1) ℂ * diag d * GeneralLinear.weylLong (r + 1) ℂ =
      diag (fun i => d i.rev) := by
  apply Units.ext
  ext i j
  change (GeneralLinear.weylLong (r + 1) ℂ * diag d *
    GeneralLinear.weylLong (r + 1) ℂ) i j = (diag fun i => d i.rev) i j
  rw [GeneralLinear.weylLong_conjugate_entry]
  simp [Matrix.diagonal_apply]

private theorem dual_diagonal (a : ℂˣ) :
    GeneralLinear.weylLong (r + 1) ℂ *
        GeneralLinear.inverseTranspose (r + 1) ℂ (changeDiagonal r a) *
        GeneralLinear.weylLong (r + 1) ℂ =
      changeDiagonal r a * GeneralLinear.scalar ((a ^ r)⁻¹) := by
  rw [changeDiagonal, inverseTranspose_diagonal, longWeyl_conj_diagonal,
    ← diagonal_const, ← map_mul]
  congr 1
  funext i
  change (a ^ (r - i.rev.val))⁻¹ = a ^ (r - i.val) * (a ^ r)⁻¹
  have hsum : (r - i.rev.val) + (r - i.val) = r := by
    have hi := i.isLt
    rw [Fin.val_rev]
    omega
  have hpow : a ^ (r - i.rev.val) * a ^ (r - i.val) = a ^ r := by
    rw [← pow_add, hsum]
  rw [← hpow, mul_inv_rev, mul_inv_cancel_left]

private theorem dual_shift_point (a : ℂˣ) (g : G) :
    (changeDiagonal r a)⁻¹ *
        (GeneralLinear.weylLong (r + 1) ℂ *
          GeneralLinear.inverseTranspose (r + 1) ℂ
            (changeDiagonal r a * g * GeneralLinear.scalar a)) =
      (GeneralLinear.weylLong (r + 1) ℂ * GeneralLinear.inverseTranspose (r + 1) ℂ g) *
        GeneralLinear.scalar ((a ^ (r + 1))⁻¹) := by
  let t := changeDiagonal r a
  let w := GeneralLinear.weylLong (r + 1) ℂ
  let ι := GeneralLinear.inverseTranspose (r + 1) ℂ
  let z : ℂˣ →* G := GeneralLinear.scalar
  have hz : ι (z a) = z a⁻¹ := by
    change GeneralLinear.inverseTranspose (r + 1) ℂ (GeneralLinear.scalar a) = _
    rw [← diagonal_const, inverseTranspose_diagonal]
    rfl
  change t⁻¹ * (w * ι (t * g * z a)) = w * ι g * z ((a ^ (r + 1))⁻¹)
  rw [map_mul, map_mul, hz]
  calc
    _ = t⁻¹ * (w * ι t * (w * w) * ι g * z a⁻¹) := by
      rw [show w * w = 1 from GeneralLinear.weylLong_mul_self _ _]
      simp only [mul_one, mul_assoc]
    _ = t⁻¹ * (w * ι t * w) * (w * ι g) * z a⁻¹ := by group
    _ = (w * ι g) * (z ((a ^ r)⁻¹) * z a⁻¹) := by
      rw [show w * ι t * w = t * z ((a ^ r)⁻¹) from dual_diagonal a, inv_mul_cancel_left,
        Matrix.GeneralLinearGroup.scalar_commute ((a ^ r)⁻¹) (w * ι g), mul_assoc]
    _ = _ := by rw [← map_mul, ← mul_inv_rev, ← pow_succ']

private theorem dual_translate {ds : List ComplexCharacterData} {b : ℂˣ} {W : G → ℂ}
    (hlen : ds.length = r + 1) (hW : W ∈ complexWhittakerModel r ds b) (a : ℂˣ) (g : G) :
    ArchimedeanLocal.dualFunction (r + 1) (leftTranslate (changeDiagonal r a)⁻¹ W)
        (changeDiagonal r a * g * GeneralLinear.scalar a) =
      (centralCharacter ds ((a ^ (r + 1))⁻¹) : ℂ) * ArchimedeanLocal.dualFunction (r + 1) W g := by
  unfold ArchimedeanLocal.dualFunction
  rw [leftTranslate_apply, dual_shift_point, model_mul_scalar hlen hW]

/-- Changing the character changes the Fourier-argument scale and contributes the
product-measure scale `|a|^n`. -/
theorem fourier_scale (a : ℂˣ) {n : ℕ} (Φ : (Fin n → ℂ) → ℂ) (x : Fin n → ℂ) :
    complexFourierTransform a Φ x =
      (‖(a : ℂ)‖ : ℂ) ^ n * complexFourierTransform 1 Φ ((a : ℂ) • x) := by
  have hμ : (complexSelfDualMeasure a).measure =
      ‖(a : ℂ)‖₊ • (complexSelfDualMeasure 1).measure := by
    simp only [complexSelfDualMeasure, complexScaledMeasure_measure, Units.val_one, nnnorm_one,
      one_mul, smul_smul]
  unfold complexFourierTransform ArchimedeanLocal.fourierTransform
  simp only [hμ, HarmonicAnalysis.pi_nnreal_smul, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul,
    NNReal.coe_pow, coe_nnnorm, Complex.ofReal_pow]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  change (complexScaledCharacter a (∑ j, y j * x j) : ℂ) =
    (complexScaledCharacter 1 (∑ j, y j * ((a : ℂ) • x) j) : ℂ)
  have hsum : (a : ℂ) * (∑ j, y j * x j) = ∑ j, y j * ((a : ℂ) • x) j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp only [Pi.smul_apply, smul_eq_mul]; ring
  simp only [complexScaledCharacter_apply, Units.val_one, one_mul, hsum]

/-- Translation of a Whittaker coefficient by the inverse change-of-character diagonal. -/
def normalizeWhittaker (a : ℂˣ) (W : G → ℂ) : G → ℂ :=
  leftTranslate (changeDiagonal r a)⁻¹ W

theorem normalizeWhittaker_mem {ds : List ComplexCharacterData} {a : ℂˣ} {W : G → ℂ}
    (hW : W ∈ complexWhittakerModel r ds a) :
    normalizeWhittaker a W ∈ complexWhittakerModel r ds 1 := by
  simpa only [normalizeWhittaker, mul_inv_cancel] using leftTranslate_mem_model a a hW

theorem normalizeWhittaker_neg_mem {ds : List ComplexCharacterData} {a : ℂˣ} {W : G → ℂ}
    (hW : W ∈ complexWhittakerModel r ds (-a)) :
    normalizeWhittaker a W ∈ complexWhittakerModel r ds (-1) := by
  simpa only [normalizeWhittaker, neg_mul, mul_inv_cancel] using leftTranslate_mem_model a (-a) hW

/-- Scalar multiplying the standard-character primal integral. -/
def primalMultiplier (r : ℕ) (a : ℂˣ) (s : ℂ) : ℂ :=
  amplitude a (-(r : ℂ) * (r + 1) * s)

/-- Scalar multiplying the standard-character dual integral. -/
def dualMultiplier (r : ℕ) (ds ds' : List ComplexCharacterData) (a : ℂˣ) (s : ℂ) : ℂ :=
  ((centralCharacter ds a : ℂ) * (centralCharacter ds' a : ℂ)) ^ (r + 1) *
    amplitude a ((r + 1) - (r + 1) * (r + 2) * s)

private theorem dualMultiplier_ne_zero (ds ds' : List ComplexCharacterData) (a : ℂˣ) (s : ℂ) :
    dualMultiplier r ds ds' a s ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (mul_ne_zero (centralCharacter ds a).ne_zero
    (centralCharacter ds' a).ne_zero)) (amplitude_ne_zero _ _)

private theorem amplitude_cancel (a : ℂˣ) (s : ℂ) :
    amplitude a (-s) * amplitude a s = 1 := by
  rw [← amplitude_add, neg_add_cancel]
  simp [amplitude]

private theorem primal_integrand_shift {ds ds' : List ComplexCharacterData} {a : ℂˣ}
    {W W' : G → ℂ} (hW : W ∈ complexWhittakerModel r ds a)
    (hW' : W' ∈ complexWhittakerModel r ds' (-a)) (Φ : (Fin (r + 1) → ℂ) → ℂ) (s : ℂ) :
    complexEqualIntegrand W W' Φ s =
      fun q => primalMultiplier r a s * complexEqualIntegrand
        (normalizeWhittaker a W) (normalizeWhittaker a W') Φ s (shiftQuotient a 1 q) := by
  funext q
  induction q using Quotient.inductionOn with
  | _ g =>
    rw [shiftQuotient_mk, mul_one, complexEqualIntegrand_mk (model_pair_invariant hW hW'),
      complexEqualIntegrand_mk
        (model_pair_invariant (normalizeWhittaker_mem hW) (normalizeWhittaker_neg_mem hW'))]
    have hrow : row (changeDiagonal r a * g) = row g := by
      funext j
      simpa only [map_one, mul_one, Units.val_one, one_mul] using lastRow_shift a 1 g j
    simp only [normalizeWhittaker, leftTranslate_apply, inv_mul_cancel_left, hrow, detWeight_mul,
      detWeight_changeDiagonal, primalMultiplier]
    rw [show -(r : ℂ) * (r + 1) * s = -((r : ℂ) * (r + 1) * s) by ring]
    symm
    calc
      _ = (amplitude a (-((r : ℂ) * (r + 1) * s)) * amplitude a ((r : ℂ) * (r + 1) * s)) *
          (W g * W' g * Φ (row g) * detWeight g s) := by ring
      _ = _ := by rw [amplitude_cancel, one_mul]

private theorem central_factors_cancel
    (ds ds' : List ComplexCharacterData) (a : ℂˣ) (n : ℕ) :
    ((centralCharacter ds a : ℂ) * (centralCharacter ds' a : ℂ)) ^ n *
      ((centralCharacter ds ((a ^ n)⁻¹) : ℂ) * (centralCharacter ds' ((a ^ n)⁻¹) : ℂ)) = 1 := by
  have h (d : List ComplexCharacterData) : (centralCharacter d a : ℂ) ^ n *
      (centralCharacter d ((a ^ n)⁻¹) : ℂ) = 1 := by
    rw [map_inv, map_pow, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    exact mul_inv_cancel₀ (pow_ne_zero _ (centralCharacter d a).ne_zero)
  rw [mul_pow, mul_mul_mul_comm, h, h, one_mul]

private theorem dual_integrand_shift {ds ds' : List ComplexCharacterData} {a : ℂˣ}
    {W W' : G → ℂ} (hlen : ds.length = r + 1) (hlen' : ds'.length = r + 1)
    (hW : W ∈ complexWhittakerModel r ds a) (hW' : W' ∈ complexWhittakerModel r ds' (-a))
    (Φ : (Fin (r + 1) → ℂ) → ℂ) (s : ℂ) :
    complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (complexFourierTransform a Φ) s =
      fun q => dualMultiplier r ds ds' a s * complexEqualIntegrand
        (ArchimedeanLocal.dualFunction (r + 1) (normalizeWhittaker a W))
        (ArchimedeanLocal.dualFunction (r + 1) (normalizeWhittaker a W'))
        (complexFourierTransform 1 Φ) s (shiftQuotient a (GeneralLinear.scalar a) q) := by
  funext q
  induction q using Quotient.inductionOn with
  | _ g =>
    rw [shiftQuotient_mk, complexEqualIntegrand_mk (dual_pair_invariant hW hW'),
      complexEqualIntegrand_mk
        (dual_pair_invariant (normalizeWhittaker_mem hW) (normalizeWhittaker_neg_mem hW'))]
    have hrow : row (changeDiagonal r a * g * GeneralLinear.scalar a) = (a : ℂ) • row g := by
      funext j
      exact lastRow_shift a a g j
    simp only [normalizeWhittaker, dual_translate hlen hW, dual_translate hlen' hW', hrow,
      detWeight_mul, detWeight_changeDiagonal, detWeight_scalar, dualMultiplier]
    rw [fourier_scale a Φ (row g), ← amplitude_natCast]
    have hscale : amplitude a ((r + 1 - (r + 1) * (r + 2) * s : ℂ)) *
        (amplitude a ((r : ℂ) * (r + 1) * s) * amplitude a (2 * (r + 1) * s)) =
        amplitude a ((r + 1 : ℕ) : ℂ) := by
      rw [← amplitude_add, ← amplitude_add]
      congr 1
      push_cast
      ring
    symm
    calc
      _ = (((centralCharacter ds a : ℂ) * (centralCharacter ds' a : ℂ)) ^ (r + 1) *
          ((centralCharacter ds ((a ^ (r + 1))⁻¹) : ℂ) *
            (centralCharacter ds' ((a ^ (r + 1))⁻¹) : ℂ))) *
          (amplitude a ((r : ℂ) + 1 - (r + 1) * (r + 2) * s) *
            (amplitude a ((r : ℂ) * (r + 1) * s) * amplitude a (2 * (r + 1) * s))) *
          (ArchimedeanLocal.dualFunction (r + 1) W g *
            ArchimedeanLocal.dualFunction (r + 1) W' g *
            complexFourierTransform 1 Φ ((a : ℂ) • row g) * detWeight g s) := by ring
      _ = _ := by rw [central_factors_cancel, one_mul, hscale]; ring

private theorem compare_under_shift (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (z : G) {c : ℂ} (hc : c ≠ 0) {f F : Q → ℂ}
    (h : f = fun q => c * F (shiftQuotient a z q)) :
    (Integrable f D.measure ↔ Integrable F (changeQuotientMeasure a D).measure) ∧
      (∫ q, f q ∂D.measure) = c * ∫ q, F q ∂(changeQuotientMeasure a D).measure := by
  subst f
  have hm := measurePreserving_shiftQuotient a D z
  have he := (shiftQuotient a z).measurableEmbedding
  refine ⟨(integrable_const_mul_iff (isUnit_iff_ne_zero.mpr hc) _).trans
    (hm.integrable_comp_emb he), ?_⟩
  rw [integral_const_mul, hm.integral_comp he]

theorem primal_comparison {ds ds' : List ComplexCharacterData} {a : ℂˣ}
    {W W' : G → ℂ} (hW : W ∈ complexWhittakerModel r ds a)
    (hW' : W' ∈ complexWhittakerModel r ds' (-a)) (D : ComplexQuotientMeasureData r)
    (Φ : (Fin (r + 1) → ℂ) → ℂ) (s : ℂ) :
    (Integrable (complexEqualIntegrand W W' Φ s) D.measure ↔
      Integrable (complexEqualIntegrand (normalizeWhittaker a W) (normalizeWhittaker a W') Φ s)
        (changeQuotientMeasure a D).measure) ∧
    complexEqualIntegral D W W' Φ s =
      primalMultiplier r a s *
        complexEqualIntegral (changeQuotientMeasure a D)
          (normalizeWhittaker a W) (normalizeWhittaker a W') Φ s :=
  compare_under_shift a D 1 (amplitude_ne_zero _ _) (primal_integrand_shift hW hW' Φ s)

theorem dual_comparison {ds ds' : List ComplexCharacterData} {a : ℂˣ}
    {W W' : G → ℂ} (hlen : ds.length = r + 1) (hlen' : ds'.length = r + 1)
    (hW : W ∈ complexWhittakerModel r ds a) (hW' : W' ∈ complexWhittakerModel r ds' (-a))
    (D : ComplexQuotientMeasureData r) (Φ : (Fin (r + 1) → ℂ) → ℂ) (s : ℂ) :
    (Integrable (complexEqualIntegrand (ArchimedeanLocal.dualFunction (r + 1) W)
        (ArchimedeanLocal.dualFunction (r + 1) W') (complexFourierTransform a Φ) s) D.measure ↔
      Integrable (complexEqualIntegrand
        (ArchimedeanLocal.dualFunction (r + 1) (normalizeWhittaker a W))
        (ArchimedeanLocal.dualFunction (r + 1) (normalizeWhittaker a W'))
        (complexFourierTransform 1 Φ) s) (changeQuotientMeasure a D).measure) ∧
    complexEqualDualIntegral a D W W' Φ s =
      dualMultiplier r ds ds' a s *
        complexEqualDualIntegral 1 (changeQuotientMeasure a D)
          (normalizeWhittaker a W) (normalizeWhittaker a W') Φ s :=
  compare_under_shift a D (GeneralLinear.scalar a) (dualMultiplier_ne_zero ds ds' a s)
    (dual_integrand_shift hlen hlen' hW hW' Φ s)

end Langlands.Global.RankinSelbergGlobal.ComplexCharacterChange
