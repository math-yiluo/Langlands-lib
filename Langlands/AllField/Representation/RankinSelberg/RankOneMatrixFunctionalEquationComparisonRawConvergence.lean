import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonRawConvergence
import Langlands.AllField.Representation.RankinSelberg.IntegralDeterminant
import Langlands.AllField.Representation.RankinSelberg.IwasawaHaarIntegration
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonMatrixBoxDiagonalBound
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonTorusEnvelope
import Langlands.AllField.Representation.RankinSelberg.UnipotentDiagonalVolume
/-! Raw coefficient-model matrix convergence from the supplied matrix bounds. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairGammaFactor QuotientHaarExistenceStatement TorusCoefficientEnvelope UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement biSmooth_matrixDiagonal_convergesOnRight boundedDiagonalNormIntegrand boundedDiagonalNormIntegrand_convergesOnRight boundedDiagonalNormIntegrand_le_matrixDiagonal boxDiagonalLocalField boxDiagonalTopology boxDiagonalUnitsBorel boxDiagonalUnitsMeasurable boxDiagonalValuativeRel diagonalBorelDensity diagonalConj_map diagonalSliceWeight diagonalSliceWeight_nonneg enorm_weightedCoefficient_sub_natCast exists_uniform_matrixUnipotentNormSlice_bound glCoefficientModel_isOfWhittakerType integrable_biSmooth_matrixDiagonalIntegrand integrable_diagonalUnits_of_principalFixed isClopen_matrixNormBox isCompact_matrixNormBox lintegral_iwasawa_diagonalBorelDensity lintegral_norm_matrixIntegrand_iwasawa matrixComparisonModelsTopology matrixConvergesOnRight_inverseTransposePullback matrixConvergesOnRight_of_torusEnvelope matrixDiagonalIntegrand matrixIntegrand_exists_principalFixed matrixNormBox matrixNormBoxTest matrixNormBoxTest_diagonal_of_le matrixUnipotentNormSlice measurable_biSmooth_matrixIntegrand measurable_boundedDiagonalNormIntegrand measure_diagonalUnits_preimage_principalLevel_le_one normalizedAbs_det_of_mem_integralSubgroup normalizedAbsoluteValue normalizedAbsoluteValue_apply rawMatrixGLBorel rawMatrixGLMeasurable rawMatrixLocalField rawMatrixNBorel rawMatrixNMeasurable rawMatrixSecondCountable rawMatrixT2 rawMatrixTopology rawMatrixUnitsBorel rawMatrixUnitsMeasurable rawMatrixUnitsSecondCountable rawMatrixValuativeRel singleton_modulus_real smoothDiagonalGLBorel smoothDiagonalGLLocallyCompact smoothDiagonalGLMeasurable smoothDiagonalGLSecondCountable smoothDiagonalLocalField smoothDiagonalSecondCountable smoothDiagonalT2 smoothDiagonalTopology smoothDiagonalUnitsBorel smoothDiagonalUnitsMeasurable smoothDiagonalUnitsSecondCountable smoothDiagonalValuativeRel smoothTorusGLBorel smoothTorusGLMeasurable smoothTorusLocalField smoothTorusTopology smoothTorusValuativeRel torusCoefficientEnvelope_of_smooth torusEnvelopeLocalField torusEnvelopeTopology torusEnvelopeValuation unipotentHaar_mul_diagonal_le unipotentVolumeLocalField unipotentVolumeTopology unipotentVolumeValuativeRel whittakerCoefficient_matrixConvergesOnRight_of_matrix
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Topology
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear
open Langlands.Conductor
open Langlands.GodementJacquet
open Langlands.AllField.GodementJacquet
open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open scoped ENNReal NNReal

universe uF uV

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance rawMatrixT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance rawMatrixSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance rawMatrixGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance rawMatrixGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

local instance rawMatrixUnitsSecondCountable : SecondCountableTopology Fˣ :=
  Units.isEmbedding_val₀.secondCountableTopology
local instance rawMatrixUnitsMeasurable : MeasurableSpace Fˣ := borel _
local instance rawMatrixUnitsBorel : BorelSpace Fˣ := ⟨rfl⟩

local instance rawMatrixNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance rawMatrixNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩

/-- The genuine unipotent norm slice of a full-matrix test. -/
def matrixUnipotentNormSlice {n : ℕ} (Φ : MatrixTestFunction n F)
    (a : Fin (n + 1) → Fˣ) (k : Langlands.GeneralLinear (n + 1) F) : ℝ≥0∞ :=
  ∫⁻ u : upperUnipotent (n + 1) F,
    ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val)‖ₑ
      ∂unipotentHaar F n

/-- One slice bound works uniformly for every integral right factor.
The bounded diagonal cutoff is pointwise and precedes integration. -/
theorem exists_uniform_matrixUnipotentNormSlice_bound {n : ℕ}
    (Φ : MatrixTestFunction n F) :
    ∃ B : ℝ, 0 ≤ B ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∃ e : Fin (n + 1) → ℕ,
      ∀ k ∈ integralSubgroup (ValuativeRel.valuation F).integer n,
      ∀ a : Fin (n + 1) → Fˣ,
        matrixUnipotentNormSlice F Φ a k ≤
          if ∀ i, abv (a i : F) ≤ ρ then
            ENNReal.ofReal B * ENNReal.ofReal (∏ i, (abv (a i : F))⁻¹ ^ e i)
          else 0 := by
  classical
  obtain ⟨B, hB⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let K : Set (Langlands.GeneralLinear (n + 1) F) :=
    integralSubgroup (ValuativeRel.valuation F).integer n
  have hK : IsCompact K := by
    dsimp only [K]
    rw [← principalLevelSubgroup_zero F n]
    exact isCompact_principalLevelOpenSubgroup F n 0
  let L : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F) :=
    (fun z : Matrix (Fin (n + 1)) (Fin (n + 1)) F ×
        Langlands.GeneralLinear (n + 1) F => z.1 * z.2⁻¹.val) ''
      ((tsupport (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ)) ×ˢ K)
  have hL : IsCompact L := (Φ.hasCompactSupport.prod hK).image
    (continuous_fst.matrix_mul (Units.continuous_val.comp continuous_snd.inv))
  obtain ⟨r, C, e, hvol⟩ := unipotentHaar_mul_diagonal_le n L hL
  refine ⟨B * |C|, mul_nonneg hB0 (abs_nonneg C), abv (r : F),
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).pos r.ne_zero, e, ?_⟩
  intro k hk a
  let E : Set (upperUnipotent (n + 1) F) :=
    {u | u.val.val * Matrix.diagonal (fun i => (a i : F)) ∈ L}
  have hpt : ∀ u : upperUnipotent (n + 1) F,
      ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val)‖ₑ ≤
        E.indicator (fun _ => ENNReal.ofReal B) u := by
    intro u
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    · have hnot : u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val ∉
          tsupport (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F → ℂ) := by
        intro h
        apply hu
        refine ⟨(u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val, k),
          ⟨h, hk⟩, ?_⟩
        change u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val * k⁻¹.val = _
        rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      rw [image_eq_zero_of_notMem_tsupport hnot, enorm_zero]
      exact zero_le
  have hpre : matrixUnipotentNormSlice F Φ a k ≤
      ENNReal.ofReal B * unipotentHaar F n E :=
    (lintegral_mono hpt).trans (lintegral_indicator_const_le E _)
  split_ifs with ha
  · have hM : 0 ≤ ∏ i, (abv (a i : F))⁻¹ ^ e i :=
      Finset.prod_nonneg fun i _ =>
        pow_nonneg (inv_nonneg.mpr ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).nonneg _)) _
    refine hpre.trans ?_
    rw [ENNReal.ofReal_mul hB0, mul_assoc]
    apply mul_le_mul' le_rfl
    refine (hvol a).2.trans ?_
    rw [← ENNReal.ofReal_mul (abs_nonneg C)]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self C) hM)
  · have hE : E = ∅ :=
      Set.eq_empty_iff_forall_notMem.mpr fun u hu => ha ((hvol a).1 ⟨u, hu⟩)
    simpa only [hE, measure_empty, mul_zero] using hpre

/-- The exact inverse upper-Borel density in diagonal coordinates. -/
def diagonalBorelDensity {n : ℕ} (a : Fin (n + 1) → Fˣ) : ℝ≥0∞ :=
  ENNReal.ofReal ((∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter
    (fun j : Fin (n + 1) => i < j), abv (a i : F) / abv (a j : F))⁻¹)

/-- Iwasawa integration with the unchanged normalized group and torus Haar
measures, expressed in the density used by the diagonal bound. -/
theorem lintegral_iwasawa_diagonalBorelDensity {n : ℕ}
    (f : Langlands.GeneralLinear (n + 1) F → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ g, f g ∂generalLinearHaar F n =
      ∫⁻ k in (integralSubgroup (ValuativeRel.valuation F).integer n :
          Set (Langlands.GeneralLinear (n + 1) F)),
        ∫⁻ a, diagonalBorelDensity F a *
          ∫⁻ u : upperUnipotent (n + 1) F,
            f (u.val * Iwasawa.diagonalUnits a * k) ∂unipotentHaar F n
          ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F)
        ∂generalLinearHaar F n := by
  refine IwasawaHaar.lintegral_generalLinearHaar (diagonalBorelDensity F) (fun a => ?_) f hf
  rw [diagonalConj_map F (⟨⟩ : LocalFieldData F) n a, ENNReal.smul_def]
  congr 1
  rw [← ENNReal.ofReal_coe_nnreal, NNReal.coe_inv, singleton_modulus_real F _ a]
  unfold diagonalBorelDensity
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  change abv ((a i / a j : Fˣ) : F) =
    abv (a i : F) / abv (a j : F)
  rw [Units.val_div_eq_div_val, map_div₀]

/-- Measurability of a bounded diagonal geometric norm integrand. -/
theorem measurable_boundedDiagonalNormIntegrand {n : ℕ}
    (e : Fin (n + 1) → ℕ) (ρ : ℝ) (s : ℂ)
    (f : Langlands.GeneralLinear (n + 1) F → ℂ) (hf : Continuous f) :
    Measurable (boundedDiagonalNormIntegrand F e ρ s f) := by
  have hcoord (i : Fin (n + 1)) :
      Measurable (fun a : Fin (n + 1) → Fˣ => abv (a i : F)) :=
    ((⟨⟩ : LocalFieldData F).continuous_normalizedAbs.comp
      (Units.continuous_val.comp (continuous_apply i))).measurable
  have hbox : MeasurableSet {a : Fin (n + 1) → Fˣ |
      ∀ i, abv (a i : F) ≤ ρ} := by
    have hsets (i : Fin (n + 1)) : MeasurableSet
        {a : Fin (n + 1) → Fˣ | abv (a i : F) ≤ ρ} :=
      measurableSet_le (hcoord i) measurable_const
    simpa only [Set.ofPred_forall] using MeasurableSet.iInter hsets
  have hw : Measurable (diagonalSliceWeight F e) := by
    unfold diagonalSliceWeight
    exact (Finset.measurable_prod _ fun i hi => Finset.measurable_prod _
      fun j hj => (hcoord i).div (hcoord j)).inv.mul
        (Finset.measurable_prod _ fun i hi => (hcoord i).inv.pow_const (e i))
  have hdet : Measurable fun g : Langlands.GeneralLinear (n + 1) F =>
      determinantWeight abv g s := by
    unfold determinantWeight
    exact (Complex.continuous_ofReal.comp
      ((⟨⟩ : LocalFieldData F).continuous_normalizedAbs.comp
        Units.continuous_val.matrix_det)).measurable.pow_const s
  have hnorm : Measurable fun a : Fin (n + 1) → Fˣ =>
      ‖f (Iwasawa.diagonalUnits a) * determinantWeight abv (Iwasawa.diagonalUnits a) s‖ₑ :=
    (((hf.comp (continuous_diagonalUnits (n + 1))).measurable).mul
      (hdet.comp (continuous_diagonalUnits (n + 1)).measurable)).enorm
  exact (hw.ennreal_ofReal.mul hnorm).ite hbox measurable_const

/-- Left standard equivariance removes the unipotent character from the
actual norm slice, while the integral right factor has determinant norm one. -/
theorem lintegral_norm_matrixIntegrand_iwasawa {n : ℕ}
    (ψ : UnitaryAdditiveCharacter F)
    (W : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hW : ∀ u : upperUnipotent (n + 1) F, ∀ g,
      W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g)
    (Φ : MatrixTestFunction n F) (s : ℂ)
    (a : Fin (n + 1) → Fˣ)
    (k : Langlands.GeneralLinear (n + 1) F)
    (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
    ∫⁻ u : upperUnipotent (n + 1) F,
      ‖matrixIntegrand abv Φ s W (u.val * Iwasawa.diagonalUnits a * k)‖ₑ
        ∂unipotentHaar F n =
      ‖W (Iwasawa.diagonalUnits a * k) * determinantWeight abv (Iwasawa.diagonalUnits a) s‖ₑ *
        matrixUnipotentNormSlice F Φ a k := by
  have hweight : determinantWeight abv (Iwasawa.diagonalUnits a * k) s =
      determinantWeight abv (Iwasawa.diagonalUnits a) s := by
    have hkdet : abv (Matrix.det k.val) = 1 :=
      normalizedAbs_det_of_mem_integralSubgroup (⟨⟩ : LocalFieldData F) hk
    simp only [determinantWeight, Units.val_mul, Matrix.det_mul, map_mul, hkdet, mul_one]
  have hpoint (u : upperUnipotent (n + 1) F) :
      ‖matrixIntegrand abv Φ s W (u.val * Iwasawa.diagonalUnits a * k)‖ₑ =
        ‖W (Iwasawa.diagonalUnits a * k) * determinantWeight abv (Iwasawa.diagonalUnits a) s‖ₑ *
          ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F)) * k.val)‖ₑ := by
    have hc : ‖(standardCharacter ψ n u : ℂ)‖ₑ = 1 := by
      rw [← ofReal_norm, norm_standardCharacter, ENNReal.ofReal_one]
    unfold matrixIntegrand
    rw [mul_assoc u.val, determinantWeight_unipotent_mul, hweight, hW]
    simp only [enorm_mul, hc, one_mul, Units.val_mul, Iwasawa.diagonalUnits_val]
    rw [Matrix.mul_assoc]
    ring
  simp_rw [hpoint]
  exact lintegral_const_mul' _ _ enorm_ne_top

/-- A finite actual coefficient envelope, together with the supplied matrix
half-plane, gives genuine raw matrix convergence. -/
theorem matrixConvergesOnRight_of_torusEnvelope
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hMatrix : Langlands.AllField.GodementJacquet.Padic.MatrixConvergesOnRight F σ)
    (W : Langlands.GeneralLinear (n + 1) F → ℂ) (hc : Continuous W)
    (heq : ∀ u : upperUnipotent (n + 1) F, ∀ g,
      W (u.val * g) = (standardCharacter ψ n u : ℂ) * W g)
    (S : Finset (biSmoothMatrixCoefficients σ))
    (henv : ∀ (a : Fin (n + 1) → Fˣ)
      (k : Langlands.GeneralLinear (n + 1) F),
      k ∈ integralSubgroup (ValuativeRel.valuation F).integer n →
      ‖W (Iwasawa.diagonalUnits a * k)‖ ≤ ∑ f ∈ S, ‖f.val (Iwasawa.diagonalUnits a)‖)
    (Φ : MatrixTestFunction n F) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re → Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s W := by
  classical
  obtain ⟨B, hB, ρ, hρ, e, hslice⟩ := exists_uniform_matrixUnipotentNormSlice_bound F Φ
  obtain ⟨b, hb⟩ := boundedDiagonalNormIntegrand_convergesOnRight F σ hMatrix e hρ
  refine ⟨b, fun s hs => ?_⟩
  have hdet : Measurable fun g : Langlands.GeneralLinear (n + 1) F =>
      determinantWeight abv g s := by
    unfold determinantWeight
    exact (Complex.continuous_ofReal.comp
      ((⟨⟩ : LocalFieldData F).continuous_normalizedAbs.comp
        Units.continuous_val.matrix_det)).measurable.pow_const s
  have hm : Measurable (matrixIntegrand abv Φ s W) :=
    ((Φ.continuous.comp Units.continuous_val).measurable.mul hc.measurable).mul hdet
  have henvE (a : Fin (n + 1) → Fˣ)
      (k : Langlands.GeneralLinear (n + 1) F)
      (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
      ‖W (Iwasawa.diagonalUnits a * k)‖ₑ ≤ ∑ f ∈ S, ‖f.val (Iwasawa.diagonalUnits a)‖ₑ := by
    have h := ENNReal.ofReal_le_ofReal (henv a k hk)
    rw [ENNReal.ofReal_sum_of_nonneg (fun f hf => norm_nonneg _)] at h
    simpa only [ofReal_norm] using h
  have hpt (k : Langlands.GeneralLinear (n + 1) F)
      (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n)
      (a : Fin (n + 1) → Fˣ) :
      diagonalBorelDensity F a *
          (∫⁻ u : upperUnipotent (n + 1) F,
            ‖matrixIntegrand abv Φ s W (u.val * Iwasawa.diagonalUnits a * k)‖ₑ
              ∂unipotentHaar F n) ≤
        ENNReal.ofReal B * ∑ f ∈ S, boundedDiagonalNormIntegrand F e ρ s f.val a := by
    rw [lintegral_norm_matrixIntegrand_iwasawa F ψ W heq Φ s a k hk, enorm_mul]
    have hsl := hslice k hk a
    by_cases ha : ∀ i, abv (a i : F) ≤ ρ
    · simp only [ha, forall_const, ite_true] at hsl
      have hd0 : 0 ≤ (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter
          (fun j : Fin (n + 1) => i < j), abv (a i : F) / abv (a j : F))⁻¹ :=
        inv_nonneg.mpr (Finset.prod_nonneg fun i hi => Finset.prod_nonneg fun j hj =>
          div_nonneg ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).nonneg _)
            ((normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)).nonneg _))
      have hweight : diagonalBorelDensity F a *
          ENNReal.ofReal (∏ i, (abv (a i : F))⁻¹ ^ e i) =
          ENNReal.ofReal (diagonalSliceWeight F e a) := by
        exact (ENNReal.ofReal_mul hd0).symm
      calc
        _ ≤ diagonalBorelDensity F a *
            (((∑ f ∈ S, ‖f.val (Iwasawa.diagonalUnits a)‖ₑ) *
              ‖determinantWeight abv (Iwasawa.diagonalUnits a) s‖ₑ) *
              (ENNReal.ofReal B * ENNReal.ofReal
                (∏ i, (abv (a i : F))⁻¹ ^ e i))) :=
          mul_le_mul' le_rfl (mul_le_mul' (mul_le_mul' (henvE a k hk) le_rfl) hsl)
        _ = _ := by
          simp only [boundedDiagonalNormIntegrand, ha, forall_const, ite_true, enorm_mul]
          simp only [← hweight, Finset.mul_sum, Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro f hf
          ring
    · simp only [ha, ite_false] at hsl
      rw [(le_zero_iff.mp hsl), mul_zero, mul_zero]
      exact zero_le
  let Q : ℝ≥0∞ := ENNReal.ofReal B * ∑ f ∈ S,
    ∫⁻ a, boundedDiagonalNormIntegrand F e ρ s f.val a
      ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F)
  have hQ : Q < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.sum_lt_top.mpr fun f hf => hb f s hs)
  have hinner (k : Langlands.GeneralLinear (n + 1) F)
      (hk : k ∈ integralSubgroup (ValuativeRel.valuation F).integer n) :
      ∫⁻ a, diagonalBorelDensity F a *
          (∫⁻ u : upperUnipotent (n + 1) F,
            ‖matrixIntegrand abv Φ s W (u.val * Iwasawa.diagonalUnits a * k)‖ₑ
              ∂unipotentHaar F n)
        ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) ≤ Q := by
    calc
      _ ≤ ∫⁻ a, ENNReal.ofReal B * ∑ f ∈ S, boundedDiagonalNormIntegrand F e ρ s f.val a
          ∂Measure.pi (fun _ : Fin (n + 1) => localMultiplicativeHaar F) :=
        lintegral_mono (hpt k hk)
      _ = Q := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_finsetSum' _ fun f hf => (measurable_boundedDiagonalNormIntegrand F e ρ s f.val
            (biSmoothMatrixCoefficient_continuous_rightFixed σ f).1).aemeasurable]
  change Integrable (matrixIntegrand abv Φ s W) (generalLinearHaar F n)
  refine ⟨hm.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  rw [lintegral_iwasawa_diagonalBorelDensity F _ hm.enorm]
  have hKmeas : MeasurableSet (integralSubgroup
      (ValuativeRel.valuation F).integer n :
        Set (Langlands.GeneralLinear (n + 1) F)) := by
    rw [← principalLevelSubgroup_zero F n]
    exact (principalLevelOpenSubgroup F n 0).isOpen.measurableSet
  calc
    _ ≤ ∫⁻ k in (integralSubgroup (ValuativeRel.valuation F).integer n :
        Set (Langlands.GeneralLinear (n + 1) F)), Q ∂generalLinearHaar F n := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hKmeas] with k hk
      exact hinner k hk
    _ = Q := by
      simp only [lintegral_const, Measure.restrict_apply_univ,
        generalLinearHaar_integralSubgroup, mul_one]
    _ < ⊤ := hQ

/-- Smoothness supplies the finite envelope for each actual Whittaker
coefficient, so the supplied matrix bounds imply its genuine raw convergence. -/
theorem whittakerCoefficient_matrixConvergesOnRight_of_matrix
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ψ : UnitaryAdditiveCharacter F)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hσ : IsSmooth σ) (ℓ : glFunctionals ψ n σ) (v : V)
    (hMatrix : Langlands.AllField.GodementJacquet.Padic.MatrixConvergesOnRight F σ)
    (Φ : MatrixTestFunction n F) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ s (fun g => ℓ.val (σ g v)) := by
  obtain ⟨S, hS⟩ := torusCoefficientEnvelope_of_smooth F ψ σ ℓ v hσ
  exact matrixConvergesOnRight_of_torusEnvelope F ψ σ hMatrix _
    (matrixCoefficient_isLocallyConstant σ ℓ.val v (hσ v)).continuous
    (fun u g => (coefficientMap σ ℓ v).property u g) S hS Φ

/-- The actual transformed matrix half-plane is the ordinary one on the
inverse-transpose pullback representation. -/
theorem matrixConvergesOnRight_inverseTransposePullback
    {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (hIota : Langlands.AllField.GodementJacquet.Padic.IotaMatrixConvergesOnRight F σ) :
    Langlands.AllField.GodementJacquet.Padic.MatrixConvergesOnRight F (inverseTransposePullback σ) := by
  obtain ⟨b, hb⟩ := hIota
  refine ⟨b, fun Φ => ?_⟩
  exact (forall_biSmoothMatrixCoefficients_comp_equiv σ
    (inverseTransposeContinuous (n + 1) F)
    (fun f => ∀ s : ℂ, b < s.re → Langlands.AllField.GodementJacquet.Padic.MatrixConverges F Φ
      (s + jpssShift n) f)).mpr (fun f s hs => hb Φ f s hs)

end Langlands.AllField.RankinSelberg
