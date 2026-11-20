import Langlands.Global.RankinSelberg.ComplexLocalOrdinaryConvergence
import Langlands.Global.RankinSelberg.UnequalAnalyticHolomorphy
import Langlands.Representation.Archimedean.ComplexGeneralLinearHaarDensity
import Langlands.Representation.Archimedean.ComplexSwapJacquetDecay
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-! # Spectral holomorphy of the partially transformed complex Godement integral -/

noncomputable section

open MeasureTheory
open scoped Classical SchwartzMap
open Langlands.Archimedean (unitaryCompact)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementWhittaker

open ArchimedeanLocal (complexNormalizedAbs)
open ComplexLocalIwasawa
open ComplexLocalWhittakerGauge (logTorus logTorus_inv_val)
open RealConvergenceAnalysis (rootPos rootPos_nonneg sub_last_le norm_cexp_mul_ofReal)
open Langlands.Archimedean.ComplexGeneralLinearHaarDensity
open Langlands.RankinSelberg.GLDeterminantDensity (matrixWeight)

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Square" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

open scoped Matrix.Norms.Operator in
private theorem continuous_whittaker {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) : Continuous W.val :=
  (contMDiff_of_mem_complexWhittakerModel W.2).continuous

open scoped Matrix.Norms.Elementwise

/-- The matrix in (7.7), with the last inverse-transpose column appended to `h`. -/
def augmentedPoint (h : G) : Rect :=
  fun i j => Fin.lastCases (h⁻¹.val (Fin.last r) i) (h.val i) j

@[simp] theorem augmentedPoint_castSucc (h : G) (i j : Fin (r + 1)) :
    augmentedPoint h i j.castSucc = h.val i j := by
  simp [augmentedPoint]

@[simp] theorem augmentedPoint_last (h : G) (i : Fin (r + 1)) :
    augmentedPoint h i (Fin.last (r + 1)) = h⁻¹.val (Fin.last r) i := by
  simp [augmentedPoint]

theorem continuous_augmentedPoint : Continuous (augmentedPoint (r := r)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  induction j using Fin.lastCases with
  | last =>
    simp only [augmentedPoint_last]
    exact (GeneralLinear.entry (R := ℂ) (Fin.last r) i).continuous.comp continuous_inv
  | cast j =>
    simp only [augmentedPoint_castSucc]
    exact (GeneralLinear.entry (R := ℂ) i j).continuous

private theorem norm_val_le_augmentedPoint (h : G) : ‖h.val‖ ≤ ‖augmentedPoint h‖ := by
  apply (Matrix.norm_le_iff (norm_nonneg _)).mpr
  intro i j
  rw [← augmentedPoint_castSucc h i j]
  exact Matrix.norm_entry_le_entrywise_sup_norm _

private theorem mul_entry_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n)
    {a b : ℝ} (ha : 0 ≤ a) (hA : ∀ k, ‖A i k‖ ≤ a) (hB : ∀ k, ‖B k j‖ ≤ b) :
    ‖(A * B) i j‖ ≤ (n : ℝ) * (a * b) := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ k, ‖A i k * B k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, a * b := Finset.sum_le_sum fun k _ => by
      rw [norm_mul]
      exact mul_le_mul (hA k) (hB k) (norm_nonneg _) ha
    _ = _ := by simp [nsmul_eq_mul]

/-- The inverse last row controls the last logarithmic coordinate of `h⁻¹`.
The other positive coordinates are then controlled by the simple-root sum. -/
theorem inverse_log_length_le (h : G) :
    (∑ i, |alpha h⁻¹ i|) ≤ ((r + 1 : ℕ) : ℝ) *
      (Real.log (((r + 1 : ℕ) : ℝ) * (1 + ‖augmentedPoint h‖)) + rootPos (alpha h⁻¹)) := by
  let g := h⁻¹
  let k := kpart g
  let y := alpha g
  let D : ℝ := ((r + 1 : ℕ) : ℝ) * (1 + ‖augmentedPoint h‖)
  have hn : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hD : 1 ≤ D := one_le_mul_of_one_le_of_one_le hn (le_add_of_nonneg_right (norm_nonneg _))
  have hDpos := zero_lt_one.trans_le hD
  have hk (i j : Fin (r + 1)) : ‖k.val.val i j‖ ≤ 1 :=
    LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup k.2 i j
  have hB : bpart g = (npart g).val * logTorus y := by
    calc
      _ = bpart ((npart g).val * logTorus y * k.val) :=
        congrArg bpart (npart_mul_logTorus_mul_kpart g).symm
      _ = _ := bpart_iwasawa (npart g) y k
  have hBInv : (bpart g)⁻¹ = k.val * h := by
    rw [bpart, mul_inv_rev, inv_inv]
    rfl
  have hdiag (i : Fin (r + 1)) : (bpart g)⁻¹.val i i = (Real.exp (-y i) : ℂ) := by
    rw [hB, mul_inv_rev, Units.val_mul, logTorus_inv_val, Matrix.diagonal_mul]
    have hd : ((npart g).val⁻¹).val i i = 1 :=
      GeneralLinear.UpperUnipotent.entry_diag (npart g)⁻¹ i
    rw [hd, mul_one]
  have hyneg (i : Fin (r + 1)) : -y i ≤ Real.log D := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hDpos]
    have hm := mul_entry_le k.val.val h.val i i zero_le_one (hk i) (fun j =>
      (Matrix.norm_entry_le_entrywise_sup_norm h.val (i := j) (j := i)).trans
        (norm_val_le_augmentedPoint h))
    rw [one_mul] at hm
    change ‖(k.val * h).val i i‖ ≤ _ at hm
    rw [← hBInv, hdiag, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
  let l := Fin.last r
  have hylast : y l ≤ Real.log D := by
    apply Real.exp_le_exp.mp
    rw [Real.exp_log hDpos]
    have hinv (j : Fin (r + 1)) : ‖k⁻¹.val.val j l‖ ≤ 1 :=
      LinearAlgebra.TriangularUnitary.norm_le_one_of_mem_unitaryGroup k⁻¹.2 j l
    have hrow (j : Fin (r + 1)) : ‖g.val l j‖ ≤ ‖augmentedPoint h‖ := by
      change ‖h⁻¹.val l j‖ ≤ _
      rw [← augmentedPoint_last]
      exact Matrix.norm_entry_le_entrywise_sup_norm _
    have hm := mul_entry_le g.val k⁻¹.val.val l l (norm_nonneg _) hrow hinv
    change ‖(bpart g).val l l‖ ≤ _ at hm
    rw [mul_one, ← exp_alpha, Complex.norm_real, Real.norm_of_nonneg (Real.exp_nonneg _)] at hm
    exact hm.trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) (by positivity))
  have hy (i : Fin (r + 1)) : |y i| ≤ Real.log D + rootPos y := by
    rw [abs_le]
    have hneg := hyneg i
    have hi := sub_last_le y i
    have hR := rootPos_nonneg y
    change y i - y l ≤ rootPos y at hi
    constructor <;> linarith
  calc
    _ ≤ ∑ _i : Fin (r + 1), (Real.log D + rootPos y) :=
      Finset.sum_le_sum fun i _ => hy i
    _ = _ := by simp [nsmul_eq_mul, D, y, g, mul_add]

/-- The real logarithm of the normalized determinant absolute value. -/
def detLog (h : G) : ℝ := Real.log (complexNormalizedAbs h.val.det)

private theorem detLog_eq (h : G) : detLog h = 2 * ∑ i, alpha h i := by
  let b := logTorus (alpha h) * (kpart h).val
  have hdet : h.val.det = b.val.det := by
    have he : (npart h).val * b = h := by
      rw [← mul_assoc, npart_mul_logTorus_mul_kpart]
    rw [← he, Units.val_mul, Matrix.det_mul, RankinSelberg.unipotent_det, one_mul]
  have hnorm := ComplexLocalOrdinaryConvergence.norm_detPower_logTorus_mul (alpha h) (kpart h) 1
  change ‖ArchimedeanLocal.detPower complexNormalizedAbs b 1‖ = _ at hnorm
  rw [ArchimedeanLocal.detPower, norm_cexp_mul_ofReal, Complex.one_re, one_mul] at hnorm
  exact Real.exp_injective (by simpa only [detLog, hdet, mul_one] using hnorm)

private theorem detLog_inv (h : G) : detLog h = -(2 * ∑ i, alpha h⁻¹ i) := by
  have he : h⁻¹.val.det = h.val.det⁻¹ := by
    apply mul_left_cancel₀ h.det_ne_zero
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one,
      mul_inv_cancel₀ h.det_ne_zero]
  have hinv : detLog h⁻¹ = -detLog h := by
    rw [detLog, detLog, he, complexNormalizedAbs, norm_inv, inv_pow, Real.log_inv]
    rfl
  rw [detLog_eq] at hinv
  linarith

private theorem exists_whittaker_bound {ds : List ComplexCharacterData} {a : ℂˣ}
    (W : complexWhittakerModel r ds a) :
    ∃ N : ℕ, ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : G,
      ‖W.val g‖ ≤ C * Real.exp ((N : ℝ) * (∑ i, |alpha g i|) - (M : ℝ) * rootPos (alpha g)) := by
  obtain ⟨N, hN⟩ := complexWhittakerSimpleRootMajorization r ds a W
  refine ⟨N, fun M => ?_⟩
  obtain ⟨C, hc, hC⟩ := hN M []
  refine ⟨C, hc, fun g => ?_⟩
  have he := complexWhittakerModel_left_equivariant W.2 (npart g).val (npart g).2
    (logTorus (alpha g) * (kpart g).val)
  rw [← mul_assoc, npart_mul_logTorus_mul_kpart] at he
  rw [he, norm_mul]
  simpa only [complexWhittakerCharacter, HarmonicAnalysis.UnitaryAdditiveCharacter.norm_complex,
    one_mul, List.map_nil, List.prod_nil, Module.End.one_apply, rootPos] using hC (alpha g) (kpart g)

/-- The fixed factors in the partially transformed Godement integrand. -/
def kernelBase (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ))
    (W : G → ℂ) (h : G) : ℂ :=
  Φ (augmentedPoint h) * W h⁻¹ * (d.character (Langlands.GeneralLinear.determinant h) : ℂ)

private theorem norm_character_det (d : ComplexCharacterData) (h : G) :
    ‖(d.character (Langlands.GeneralLinear.determinant h) : ℂ)‖ =
      Real.exp (d.exponent.re * detLog h) := by
  have hpos : 0 < ‖h.val.det‖ := norm_pos_iff.mpr h.det_ne_zero
  rw [Langlands.Archimedean.ComplexSwapJacquet.norm_character]
  change ‖h.val.det‖ ^ (2 * d.exponent.re) = _
  rw [Real.rpow_def_of_pos hpos, detLog, complexNormalizedAbs, Real.log_pow]
  congr 1
  push_cast
  ring

private theorem schwartz_decay (Φ : 𝓢(Rect, ℂ)) (J p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ h : G,
      (1 + ‖augmentedPoint h‖) ^ J * ‖Φ (augmentedPoint h)‖ ≤
        C * ((1 + ‖h.val‖) ^ p)⁻¹ := by
  let C : ℝ := 2 ^ (J + p) *
    ((Finset.Iic (J + p, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) Φ
  refine ⟨max C 0, le_max_right _ _, fun h => ?_⟩
  rw [← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).2
  have hbound := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (J + p, 0))
    le_rfl le_rfl Φ (augmentedPoint h)
  simp only [norm_iteratedFDeriv_zero] at hbound
  calc
    _ ≤ (1 + ‖augmentedPoint h‖) ^ J * ‖Φ (augmentedPoint h)‖ *
        (1 + ‖augmentedPoint h‖) ^ p := by
      apply mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact pow_le_pow_left₀ (by positivity) (by gcongr; exact norm_val_le_augmentedPoint h) _
    _ = (1 + ‖augmentedPoint h‖) ^ (J + p) * ‖Φ (augmentedPoint h)‖ := by
      rw [pow_add]
      ring
    _ ≤ max C 0 := hbound.trans (le_max_left _ _)

/-- The Haar-density-weighted integrand has arbitrarily high polynomial decay, uniformly on
bounded intervals of the real spectral parameter. -/
theorem exists_kernel_bound {ds : List ComplexCharacterData} {a : ℂˣ}
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : complexWhittakerModel r ds a)
    (T : ℝ) (hT : 0 ≤ T) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (σ : ℝ), |σ| ≤ T → ∀ h : G,
      ‖kernelBase d Φ W.val h‖ * Real.exp ((σ - ((r + 1 : ℕ) : ℝ)) * detLog h) ≤
        C * ((1 + ‖h.val‖) ^ p)⁻¹ := by
  obtain ⟨N, hN⟩ := exists_whittaker_bound W
  let n : ℝ := (r + 1 : ℕ)
  let A := (N : ℝ) + 2 * (|d.exponent.re| + T + n)
  have hn : 1 ≤ n := by
    change (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ)
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le r)
  have hn0 : 0 ≤ n := zero_le_one.trans hn
  have hA : 0 ≤ A := by dsimp [A, n]; positivity
  obtain ⟨J, hJ⟩ := exists_nat_ge (A * n)
  obtain ⟨C₀, hC₀, hW⟩ := hN J
  obtain ⟨C₁, hC₁, hΦ⟩ := schwartz_decay Φ J p
  refine ⟨C₀ * n ^ J * C₁, by dsimp [n]; positivity, fun σ hσ h => ?_⟩
  let y := alpha h⁻¹
  let S := ∑ i, |y i|
  let R := rootPos y
  let X := augmentedPoint h
  let D := Real.log (n * (1 + ‖X‖))
  have hD : 0 ≤ D := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le hn (le_add_of_nonneg_right (norm_nonneg _))
  have hR : 0 ≤ R := rootPos_nonneg _
  have hSum : |∑ i, y i| ≤ S := Finset.abs_sum_le_sum_abs _ _
  have hcoef : |d.exponent.re + σ - n| ≤ |d.exponent.re| + T + n := by
    calc
      _ ≤ |d.exponent.re + σ| + |-n| := by
        rw [sub_eq_add_neg]
        exact abs_add_le (d.exponent.re + σ) (-n)
      _ ≤ _ := by
        rw [abs_neg, abs_of_nonneg hn0]
        have htri := abs_add_le d.exponent.re σ
        linarith
  have hweight : (d.exponent.re + σ - n) * detLog h ≤ 2 * (|d.exponent.re| + T + n) * S := by
    rw [detLog_inv]
    change (d.exponent.re + σ - n) * -(2 * ∑ i, y i) ≤ _
    refine (le_abs_self _).trans ?_
    rw [abs_mul, abs_neg, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
    have hS : 2 * |∑ i, y i| ≤ 2 * S := mul_le_mul_of_nonneg_left hSum (by norm_num)
    calc
      _ ≤ (|d.exponent.re| + T + n) * (2 * S) :=
        mul_le_mul hcoef hS (by positivity) (by positivity)
      _ = _ := by ring
  have hlen : S ≤ n * (D + R) := inverse_log_length_le h
  have hExp : (N : ℝ) * S - (J : ℝ) * R + (d.exponent.re + σ - n) * detLog h ≤
      (J : ℝ) * D := by
    have h1 := mul_le_mul_of_nonneg_left hlen hA
    have h2 := mul_le_mul_of_nonneg_right hJ (add_nonneg hD hR)
    dsimp only [A] at h1
    nlinarith only [hweight, h1, h2]
  calc
    _ = ‖W.val h⁻¹‖ * (‖Φ X‖ * Real.exp ((d.exponent.re + σ - n) * detLog h)) := by
      rw [kernelBase, norm_mul, norm_mul, norm_character_det]
      rw [show (d.exponent.re + σ - n) * detLog h =
        d.exponent.re * detLog h + (σ - n) * detLog h by ring, Real.exp_add]
      ring
    _ ≤ C₀ * Real.exp ((N : ℝ) * S - (J : ℝ) * R) *
        (‖Φ X‖ * Real.exp ((d.exponent.re + σ - n) * detLog h)) :=
      mul_le_mul_of_nonneg_right (hW h⁻¹) (by positivity)
    _ = C₀ * ‖Φ X‖ *
        Real.exp ((N : ℝ) * S - (J : ℝ) * R + (d.exponent.re + σ - n) * detLog h) := by
      rw [Real.exp_add]
      ring
    _ ≤ C₀ * ‖Φ X‖ * Real.exp ((J : ℝ) * D) :=
      mul_le_mul_of_nonneg_left (Real.exp_monotone hExp) (by positivity)
    _ = C₀ * n ^ J * ((1 + ‖X‖) ^ J * ‖Φ X‖) := by
      rw [Real.exp_nat_mul]
      dsimp only [D]
      rw [Real.exp_log (by dsimp [n]; positivity), mul_pow]
      ring
    _ ≤ C₀ * n ^ J * (C₁ * ((1 + ‖h.val‖) ^ p)⁻¹) :=
      mul_le_mul_of_nonneg_left (hΦ h) (by positivity)
    _ = _ := by ring

private theorem normalizedAbs_det_pos (h : G) : 0 < complexNormalizedAbs h.val.det :=
  pow_pos (norm_pos_iff.mpr h.det_ne_zero) _

private theorem continuous_detLog : Continuous (detLog (r := r)) := by
  have hd : Continuous (fun h : G => h.val.det) :=
    Units.continuous_val.comp (GeneralLinear.determinantContinuous (n := r + 1) (R := ℂ)).continuous
  exact (hd.norm.pow 2).log (fun h => (normalizedAbs_det_pos h).ne')

private theorem continuous_kernelBase {ds : List ComplexCharacterData} {a : ℂˣ}
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : complexWhittakerModel r ds a) :
    Continuous (kernelBase d Φ W.val) :=
  ((Φ.continuous.comp continuous_augmentedPoint).mul
    ((continuous_whittaker W).comp continuous_inv)).mul
    (Units.continuous_val.comp (d.character.continuous.comp
      (GeneralLinear.determinantContinuous (n := r + 1) (R := ℂ)).continuous))

private def tail (p : ℕ) (X : Square) : ℝ := ((1 + ‖X‖) ^ p)⁻¹

private theorem integrable_tail_with_det (p : ℕ) (hp : Module.finrank ℝ Square < p)
    (μ : Measure G) [μ.IsHaarMeasure] :
    Integrable (fun h : G => ((complexNormalizedAbs h.val.det ^ (r + 1) * tail p h.val : ℝ) : ℂ)) μ := by
  let U : Set Square := Set.range (Units.val : G → Square)
  have hU : MeasurableSet U := by
    have he : U = {X : Square | X.det ≠ 0} := by
      ext X
      constructor
      · rintro ⟨h, rfl⟩
        exact Matrix.GeneralLinearGroup.det_ne_zero h
      · intro hX
        exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero X hX, rfl⟩
    rw [he]
    exact (isOpen_ne_fun continuous_id.matrix_det continuous_const).measurableSet
  have htail : Integrable (tail p : Square → ℝ) (matrixLebesgue (r + 1)) := by
    have hi := integrable_one_add_norm (μ := matrixLebesgue (r + 1)) (r := (p : ℝ))
      (by exact_mod_cast hp)
    refine hi.congr (ae_of_all _ fun X => ?_)
    simp only [tail, Real.rpow_neg (show 0 ≤ 1 + ‖X‖ by positivity), Real.rpow_natCast]
  let F (X : Square) : ℂ := (complexNormalizedAbs X.det ^ (r + 1) * tail p X : ℝ)
  have hI : Integrable (fun h : G => F h.val) (complexGeneralLinearHaar (r + 1)) := by
    apply (integrable_complexGeneralLinearHaar_iff F).mpr
    refine (htail.ofReal.mono_measure Measure.restrict_le_self).congr ?_
    filter_upwards [ae_restrict_mem hU] with X hX
    obtain ⟨h, rfl⟩ := hX
    have hd := (normalizedAbs_det_pos h).ne'
    change (tail p h.val : ℂ) =
      ((complexNormalizedAbs h.val.det)⁻¹ ^ (r + 1) : ℝ) •
        ((complexNormalizedAbs h.val.det ^ (r + 1) * tail p h.val : ℝ) : ℂ)
    rw [Complex.real_smul, ← Complex.ofReal_mul, ← mul_assoc, ← mul_pow,
      inv_mul_cancel₀ hd, one_pow, one_mul]
  rw [Measure.isMulLeftInvariant_eq_smul μ (complexGeneralLinearHaar (r + 1))]
  exact hI.smul_measure_nnreal

private theorem integrable_moments {ds : List ComplexCharacterData} {a : ℂˣ}
    (μ : Measure G) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : complexWhittakerModel r ds a) (σ : ℝ) :
    Integrable (fun h : G => ‖kernelBase d Φ W.val h‖ * Real.exp (σ * detLog h)) μ := by
  let p := Module.finrank ℝ Square + 1
  obtain ⟨C, hC, hb⟩ := exists_kernel_bound d Φ W |σ| (abs_nonneg _) p
  let E (h : G) : ℂ := (complexNormalizedAbs h.val.det ^ (r + 1) * tail p h.val : ℝ)
  have hE : Integrable E μ := integrable_tail_with_det p (Nat.lt_succ_self _) μ
  refine (hE.norm.const_mul C).mono' ?_ ?_
  · exact ((continuous_kernelBase d Φ W).norm.mul
      (Real.continuous_exp.comp (continuous_detLog.const_mul σ))).aestronglyMeasurable
  · refine ae_of_all _ fun h => ?_
    rw [Real.norm_of_nonneg (by positivity)]
    change _ ≤ C * ‖E h‖
    dsimp only [E]
    have hE0 : 0 ≤ complexNormalizedAbs h.val.det ^ (r + 1) * tail p h.val :=
      mul_nonneg (pow_nonneg (normalizedAbs_det_pos h).le _) (by unfold tail; positivity)
    rw [Complex.norm_real, Real.norm_of_nonneg hE0]
    let n : ℝ := (r + 1 : ℕ)
    have hd : Real.exp (n * detLog h) = complexNormalizedAbs h.val.det ^ (r + 1) := by
      dsimp only [detLog, n]
      rw [Real.exp_nat_mul, Real.exp_log (normalizedAbs_det_pos h)]
    calc
      _ = ‖kernelBase d Φ W.val h‖ * Real.exp ((σ - n) * detLog h) *
          Real.exp (n * detLog h) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 2
        ring
      _ ≤ C * tail p h.val * Real.exp (n * detLog h) :=
        mul_le_mul_of_nonneg_right (hb σ le_rfl h) (Real.exp_nonneg _)
      _ = _ := by rw [hd]; ring

/-- Absolute convergence and entire dependence on the determinant exponent in the
partially transformed Godement integral, for a fixed Whittaker vector and Schwartz test. -/
def ComplexGodementWhittakerIntegralStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (μ : Measure (Langlands.GeneralLinear (r + 1) ℂ)), μ.IsHaarMeasure →
    ∀ (d : ComplexCharacterData) (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ, ℂ))
      (W : complexWhittakerModel r ds a),
      (∀ s : ℂ, Integrable (fun h => kernelBase d Φ W.val h *
        ArchimedeanLocal.detPower complexNormalizedAbs h s) μ) ∧
      Differentiable ℂ (fun s : ℂ => ∫ h, kernelBase d Φ W.val h *
        ArchimedeanLocal.detPower complexNormalizedAbs h s ∂μ)

theorem complexGodementWhittakerIntegral : ComplexGodementWhittakerIntegralStatement := by
  intro r ds a μ hμ d Φ W
  have hA := (continuous_kernelBase d Φ W).aestronglyMeasurable (μ := μ)
  have hL := continuous_detLog.aestronglyMeasurable (μ := μ)
  exact ⟨UnequalAnalytic.integrable_mul_cexp hA hL (integrable_moments μ d Φ W),
    UnequalAnalytic.differentiable_integral_mul_cexp hA hL (integrable_moments μ d Φ W)⟩

end Langlands.Global.RankinSelbergGlobal.ComplexGodementWhittaker
