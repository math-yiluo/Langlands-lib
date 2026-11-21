import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof
import Langlands.Global.RankinSelberg.ComplexMatrixSchwartzConvergence
import Langlands.Representation.Archimedean.ComplexSwapJacquetDecay

/-! # Height bounds and integrable matrix majorants for the Jacquet comparisons -/

noncomputable section

open Langlands.GeneralLinear Langlands.Archimedean Langlands.LocalFactor.Archimedean
open MeasureTheory
open scoped NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexGeneralLinearHaarDensity (complexGeneralLinearHaar)

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "H" => complexMatrixHeight

local instance jacquetMatrixMajorantMeasurable (m : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear m ℂ) := borel _
local instance jacquetMatrixMajorantBorel (m : ℕ) :
    BorelSpace (Langlands.GeneralLinear m ℂ) := ⟨rfl⟩

theorem complexMatrixHeight_nonneg (g : G) : 0 ≤ H g := by
  unfold complexMatrixHeight
  positivity

section Frobenius

open scoped Matrix.Norms.Frobenius

private theorem sq_frobenius (X : Mat) :
    ‖X‖ ^ 2 = ∑ i, ∑ j, ‖X i j‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def]
  simp only [Real.rpow_two, ← Real.sqrt_eq_rpow]
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg ‖X i j‖)

private theorem sq_frobenius_mul_le (X Y : Mat) :
    ‖X * Y‖ ^ 2 ≤ ‖X‖ ^ 2 * ‖Y‖ ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (Matrix.frobenius_norm_mul X Y) _

/-- The maximum of one and the matrix height is submultiplicative. -/
theorem max_complexMatrixHeight_mul_le (g h : G) :
    max 1 (H (g * h)) ≤ max 1 (H g) * max 1 (H h) := by
  have hg : 1 ≤ max 1 (H g) := le_max_left _ _
  have hh : 1 ≤ max 1 (H h) := le_max_left _ _
  have h₁ : 1 ≤ max 1 (H g) * max 1 (H h) := by
    simpa only [one_mul] using mul_le_mul hg hh zero_le_one (zero_le_one.trans hg)
  refine max_le h₁ ?_
  refine le_trans ?_ (mul_le_mul (le_max_right _ _) (le_max_right _ _)
    (complexMatrixHeight_nonneg _) (zero_le_one.trans hg))
  simp only [ComplexPlaceAnalytic.complexMatrixHeight_eq_frobenius, Units.val_mul, mul_inv_rev]
  refine (add_le_add (sq_frobenius_mul_le _ _) (sq_frobenius_mul_le _ _)).trans ?_
  nlinarith [mul_nonneg (sq_nonneg ‖g.val‖) (sq_nonneg ‖h⁻¹.val‖),
    mul_nonneg (sq_nonneg ‖g⁻¹.val‖) (sq_nonneg ‖h.val‖)]

end Frobenius

open scoped Matrix.Norms.Operator

theorem continuous_complexMatrixHeight : Continuous (H : G → ℝ) := by
  unfold complexMatrixHeight
  refine continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ?_
  let h : Continuous (entry (R := ℂ) i j) := (entry (R := ℂ) i j).continuous
  exact (h.norm.pow 2).add ((h.comp continuous_inv).norm.pow 2)

theorem continuous_complexDeterminant : Continuous ((determinant : G →* ℂˣ) : G → ℂˣ) := by
  apply Units.continuous_iff.mpr
  refine ⟨Units.continuous_val.matrix_det, ?_⟩
  change Continuous (fun g : G => (g⁻¹).val.det)
  exact (Units.continuous_val.comp (continuous_inv : Continuous (fun g : G => g⁻¹))).matrix_det

theorem continuous_complexDetPower (s : ℂ) :
    Continuous (fun g : G => ArchimedeanLocal.detPower complexNormalizedAbs g s) := by
  have habs : Continuous (fun g : G => complexNormalizedAbs g.val.det) :=
    Units.continuous_val.matrix_det.norm.pow 2
  have hlog := habs.log fun g => pow_ne_zero 2 (norm_ne_zero_iff.mpr (determinant g).ne_zero)
  exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hlog))

private theorem norm_matrixWeight (d : ComplexCharacterData) (Φ : Mat → ℂ) (s : ℂ) (g : G) :
    ‖Φ g.val * (d.character (determinant g) : ℂ) *
        ArchimedeanLocal.detPower complexNormalizedAbs g s‖ =
      ‖Φ g.val * ((complexNormalizedAbs g.val.det : ℝ) : ℂ) ^ (s + d.exponent)‖ := by
  let A := complexNormalizedAbs g.val.det
  have hA : 0 < A := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (determinant g).ne_zero)
  have hP : ‖ArchimedeanLocal.detPower complexNormalizedAbs g s‖ = A ^ s.re := by
    rw [ArchimedeanLocal.detPower, Complex.norm_exp, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, Real.rpow_def_of_pos hA]
    simp only [A, mul_comm]
  have hχ : ‖(d.character (determinant g) : ℂ)‖ = A ^ d.exponent.re := by
    rw [ComplexSwapJacquet.norm_character, Real.rpow_mul (norm_nonneg _), Real.rpow_two]
    rfl
  rw [norm_mul, norm_mul, hP, hχ, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hA,
    Complex.add_re, Real.rpow_add hA]
  ring

/-- Absolute integrability of a Schwartz matrix test with a height weight, a determinant
character and a determinant power under an arbitrary Haar measure on the matrix group. -/
def ComplexLocalMatrixMajorantStatement : Prop :=
  ∀ (n M : ℕ) (μ : Measure (Langlands.GeneralLinear n ℂ)) [μ.IsHaarMeasure]
    (d : ComplexCharacterData) (Φ : SchwartzMap (Matrix (Fin n) (Fin n) ℂ) ℂ) (s : ℂ),
    (n : ℝ) + M ≤ (s + d.exponent).re →
      Integrable (fun g => max 1 (H g) ^ M *
        ‖Φ g.val * (d.character (determinant g) : ℂ) *
          ArchimedeanLocal.detPower complexNormalizedAbs g s‖) μ

theorem complexLocalMatrixMajorant : ComplexLocalMatrixMajorantStatement := by
  intro n M μ _ d Φ s hs
  let ν := complexGeneralLinearHaar n
  let : LocallyCompactSpace (Langlands.GeneralLinear n ℂ) :=
    (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).locallyCompactSpace
  let : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  let : SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
    (RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) n).isInducing.secondCountableTopology
  have hμ : μ = μ.haarScalarFactor ν • ν := Measure.isMulLeftInvariant_eq_smul _ _
  rw [hμ]
  apply Integrable.smul_measure_nnreal
  have h0 : (n : ℝ) + (0 : ℕ) ≤ (s + d.exponent).re := by
    simp only [Nat.cast_zero, add_zero]
    exact (le_add_of_nonneg_right (Nat.cast_nonneg M)).trans hs
  have h0 := (ComplexMatrixSchwartz.complexMatrixSchwartzConvergence n 0 Φ (s + d.exponent) h0).norm
  have hM := (ComplexMatrixSchwartz.complexMatrixSchwartzConvergence n M Φ (s + d.exponent) hs).norm
  have hc : Continuous (fun g : Langlands.GeneralLinear n ℂ =>
      (d.character (determinant g) : ℂ)) :=
    Units.continuous_val.comp (d.character.continuous.comp continuous_complexDeterminant)
  have hcont : Continuous (fun g : Langlands.GeneralLinear n ℂ => max 1 (H g) ^ M *
      ‖Φ g.val * (d.character (determinant g) : ℂ) *
        ArchimedeanLocal.detPower complexNormalizedAbs g s‖) :=
    ((continuous_const.max continuous_complexMatrixHeight).pow M).mul
      (((Φ.continuous.comp Units.continuous_val).mul hc).mul (continuous_complexDetPower s)).norm
  refine (h0.add hM).mono' hcont.aestronglyMeasurable (ae_of_all _ fun g => ?_)
  rw [Real.norm_of_nonneg (by positivity), norm_matrixWeight]
  have hpow : max 1 (H g) ^ M ≤ 1 + H g ^ M := by
    rcases le_total (H g) 1 with h | h
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (pow_nonneg (complexMatrixHeight_nonneg _) _)
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left zero_le_one
  refine (mul_le_mul_of_nonneg_right hpow (norm_nonneg _)).trans_eq ?_
  simp only [Pi.add_apply, pow_zero, Complex.ofReal_one, one_mul, add_mul, mul_assoc,
    norm_mul, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (complexMatrixHeight_nonneg g) M)]

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
