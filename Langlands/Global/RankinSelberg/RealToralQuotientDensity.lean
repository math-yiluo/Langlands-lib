import Langlands.Global.RankinSelberg.RealIwasawaMeasure
import Langlands.Global.RankinSelberg.RealTriangularEntries

/-! # The exact real toral quotient density -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealIwasawa

open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates
  upperEntryCoordinates_apply upperEntryCoordinates_symm_upper
  upperEntryProductMeasure upperEntryProductMeasure_isHaar)
open Langlands.GodementJacquet (map_scale_realUpperEntries prod_realUpperEntryScale
  prod_realUpperEntryColumnScale)
open Langlands.QuotientIntegration (LeftQuotient)

variable {n : ℕ}

/-- The logarithm of the upper-unipotent modulus on the positive diagonal torus. -/
def torusModularLog (n : ℕ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i : Fin n, (((n - 1 - i.val : ℕ) : ℝ) - i.val) • ContinuousLinearMap.proj i

theorem torusModularLog_apply (y : Fin n → ℝ) :
    torusModularLog n y = ∑ i : Fin n, ((n : ℝ) - 1 - 2 * i.val) * y i := by
  simp only [torusModularLog, _root_.sum_apply, _root_.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : i.val ≤ n - 1 := by omega
  have hn : 1 ≤ n := by omega
  rw [Nat.cast_sub hi, Nat.cast_sub hn, Nat.cast_one]
  ring

private def scalarLebesgue : Langlands.HarmonicAnalysis.AdditiveHaarMeasure ℝ where
  measure := volume
  isAddHaar := inferInstance
  regular := inferInstance

local instance : SigmaFinite scalarLebesgue.measure :=
  inferInstanceAs (SigmaFinite (volume : Measure ℝ))

private theorem conjTorus_entry (y : Fin n → ℝ)
    (u : Langlands.GeneralLinear.upperUnipotent n ℝ) (i j : Fin n) :
    (conjTorus y u).val.val i j = Real.exp (y i - y j) * u.val.val i j := by
  change ((torus y * u.val * torus (-y)).val) i j = _
  rw [Units.val_mul, Units.val_mul, torus_val, torus_val, Matrix.mul_diagonal, Matrix.diagonal_mul]
  simp only [Pi.neg_apply, sub_eq_add_neg, Real.exp_add]
  ring

variable [MeasurableSpace (Langlands.GeneralLinear.upperUnipotent n ℝ)]
  [BorelSpace (Langlands.GeneralLinear.upperUnipotent n ℝ)]

/-- The pushforward by positive diagonal conjugation has the inverse modulus. -/
theorem map_conjTorus (μ : Measure (Langlands.GeneralLinear.upperUnipotent n ℝ))
    [μ.IsHaarMeasure] (y : Fin n → ℝ) :
    μ.map (conjTorus y) =
      ENNReal.ofReal (Real.exp (-torusModularLog n y)) • μ := by
  let e := upperEntryCoordinates n (K := ℝ)
  let ρ := upperEntryProductMeasure scalarLebesgue n
  let μ₀ := ρ.map e.symm
  let : μ₀.IsHaarMeasure := upperEntryProductMeasure_isHaar scalarLebesgue
  let : SecondCountableTopology (Langlands.GeneralLinear.upperUnipotent n ℝ) :=
    e.secondCountableTopology
  let a : Fin n → ℝˣ := fun i => Units.mk0 (Real.exp (y i)) (Real.exp_ne_zero _)
  let d : UpperEntryPair n → ℝˣ := fun ij => a ij.1.1 / a ij.1.2
  let S : (UpperEntryPair n → ℝ) → (UpperEntryPair n → ℝ) :=
    fun X ij => (d ij : ℝ) * X ij
  have hS : Measurable S :=
    (continuous_pi fun ij => continuous_const.mul (continuous_apply ij)).measurable
  have hd (ij : UpperEntryPair n) : (d ij : ℝ) = Real.exp (y ij.1.1 - y ij.1.2) := by
    simp only [d, a, Units.val_div_eq_div_val, Units.val_mk0, Real.exp_sub]
  have hcomp : conjTorus y ∘ e.symm = e.symm ∘ S := by
    funext X
    apply e.injective
    rw [Function.comp_apply, Function.comp_apply, e.apply_symm_apply]
    funext ij
    rw [show e (conjTorus y (e.symm X)) ij = (conjTorus y (e.symm X)).val.val ij.1.1 ij.1.2
          from upperEntryCoordinates_apply _ _, conjTorus_entry, ← hd]
    rw [show (e.symm X).val.val ij.1.1 ij.1.2 = X ij from
      upperEntryCoordinates_symm_upper X ij.2]
  have hprod : ((∏ ij : UpperEntryPair n, ‖(d ij : ℝ)‖₊ : ℝ≥0) : ℝ) =
      Real.exp (torusModularLog n y) := by
    calc
      _ = (((∏ ij : UpperEntryPair n, ‖(a ij.1.1 : ℝ)‖₊) /
          (∏ ij : UpperEntryPair n, ‖(a ij.1.2 : ℝ)‖₊) : ℝ≥0) : ℝ) := by
        congr 1
        rw [← Finset.prod_div_distrib]
        simp only [d, Units.val_div_eq_div_val, nnnorm_div]
      _ = _ := by
        rw [prod_realUpperEntryScale, prod_realUpperEntryColumnScale]
        have ha (i : Fin n) : (‖(a i : ℝ)‖₊ : ℝ) = Real.exp (y i) :=
          Real.norm_of_nonneg (Real.exp_pos _).le
        simp only [NNReal.coe_div, NNReal.coe_prod, NNReal.coe_pow, ha, ← Real.exp_nat_mul,
          ← Real.exp_sum, ← Real.exp_sub]
        congr 1
        simp only [torusModularLog, _root_.sum_apply, _root_.smul_apply,
          ContinuousLinearMap.proj_apply, smul_eq_mul, ← Finset.sum_sub_distrib, sub_mul]
  have hscale : (((∏ ij : UpperEntryPair n, ‖(d ij : ℝ)‖₊ : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) =
      ENNReal.ofReal (Real.exp (-torusModularLog n y)) := by
    rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, hprod, Real.exp_neg]
  have hcoord : μ₀.map (conjTorus y) =
      ENNReal.ofReal (Real.exp (-torusModularLog n y)) • μ₀ := by
    change (ρ.map e.symm).map (conjTorus y) = _
    rw [Measure.map_map (continuous_conjTorus_right y).measurable e.symm.measurable, hcomp,
      ← Measure.map_map e.symm.measurable hS, map_scale_realUpperEntries scalarLebesgue d,
      ← Measure.coe_nnreal_smul, Measure.map_smul _ e.symm.measurable.aemeasurable, hscale]
  rw [isMulLeftInvariant_eq_smul μ μ₀, ← Measure.coe_nnreal_smul,
    Measure.map_smul _ (continuous_conjTorus_right y).measurable.aemeasurable, hcoord,
    smul_comm]

variable [MeasurableSpace (Langlands.GeneralLinear n ℝ)] [BorelSpace (Langlands.GeneralLinear n ℝ)]
  [MeasurableSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))]
  [BorelSpace (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))]

/-- For compatible measures, the pushforward from the real quotient to its logarithmic
diagonal is a constant times Lebesgue measure with the inverse upper-unipotent modulus. -/
def RealToralQuotientDensityStatement : Prop :=
  ∀ (μG : Measure (Langlands.GeneralLinear n ℝ))
    (μN : Measure (Langlands.GeneralLinear.upperUnipotent n ℝ))
    [IsMulLeftInvariant μG] [IsMulRightInvariant μN] [IsHaarMeasure μN]
    (μ : Measure (LeftQuotient (Langlands.GeneralLinear.upperUnipotent n ℝ))),
    Langlands.QuotientIntegration.IsCompatible (Langlands.GeneralLinear.upperUnipotent n ℝ) μG μN μ →
    ∃ c : ℝ≥0, ∀ B : (Fin n → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂μ =
        (c : ℝ≥0∞) * ∫⁻ y, ENNReal.ofReal (Real.exp (-torusModularLog n y)) * B y

theorem realToralQuotientDensity : RealToralQuotientDensityStatement (n := n) := by
  intro μG μN _ _ _ μ hμ
  have := hμ.regular
  have := isFiniteMeasureOnCompacts_map_alphaQ μ
  obtain ⟨β, hβc, hβ, hβ0, hβ1⟩ := exists_unipotent_bump (n := n)
  have hβI : 0 < ∫ u, β u ∂μN :=
    hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hβ hβ0 (x := 1)
      (by rw [hβ1]; exact one_ne_zero)
  have htranslate (φ : (Fin n → ℝ) → ℝ) (hφc : Continuous φ) (hφ : HasCompactSupport φ)
      (z : Fin n → ℝ) :
      ∫ y, φ (z + y) ∂(μ.map alphaQ) =
        Real.exp (torusModularLog n z) * ∫ y, φ y ∂(μ.map alphaQ) := by
    have hw := weil_translate μG μN μ hμ hφc hφ hβc hβ z
    have hscale : ∫ u, β (conjTorus z u) ∂μN =
        Real.exp (-torusModularLog n z) * ∫ u, β u ∂μN := by
      rw [← integral_map (continuous_conjTorus_right z).measurable.aemeasurable
        hβc.aestronglyMeasurable, map_conjTorus, integral_smul_measure,
        ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul]
    rw [hscale] at hw
    rw [integral_map_alphaQ μ (φ := fun y => φ (z + y))
        (hφc.comp (continuous_const.add continuous_id)),
      integral_map_alphaQ μ hφc]
    apply mul_right_cancel₀ hβI.ne'
    rw [mul_assoc, ← hw]
    have he : Real.exp (torusModularLog n z) * Real.exp (-torusModularLog n z) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    rw [← mul_assoc (∫ q, φ (z + alphaQ q) ∂μ)]
    rw [← mul_assoc (Real.exp (torusModularLog n z)),
      mul_left_comm (Real.exp (torusModularLog n z)), he, mul_one]
  obtain ⟨c, hc⟩ := withDensity_eq_smul_volume (μ.map alphaQ) (torusModularLog n) htranslate
  refine ⟨c, fun B hB => ?_⟩
  rw [← lintegral_map hB measurable_alphaQ]
  exact lintegral_eq_of_withDensity_eq _ _ _ hc hB

end Langlands.Global.RankinSelbergGlobal.RealIwasawa
