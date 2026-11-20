import Langlands.Global.RankinSelberg.ComplexSquareZetaPositiveDiagonal
import Langlands.Global.RankinSelberg.ComplexGodementLogRadius
import Langlands.Representation.Archimedean.ComplexGramFormula

/-! # Angular variables in the complex square zeta integral -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator NNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexGramFormula
  (phaseUnit phaseUnit_val norm_phaseUnit diagonalUnits_phaseUnit_mem)
open ComplexGodement (upperTriangularEntries multiplicativeComplexLebesgue map_log_norm_diagonal)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squarePhaseGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squarePhaseGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance squarePhaseGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

local instance : NullSingletonClass multiplicativeComplexLebesgue := by
  unfold multiplicativeComplexLebesgue
  infer_instance

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Y" => Fin n → ℝ
local notation "Z" => Fin n → ℂ
local notation "X" => UpperEntryPair n → ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private def phaseColumns (p : Fin n → ℂˣ) (z : X) : X := fun ij => z ij * (p ij.1.2 : ℂ)

private theorem measurePreserving_phaseColumns (p : Fin n → ℂˣ) (hp : ∀ j, ‖(p j : ℂ)‖ = 1) :
    MeasurePreserving (phaseColumns p) (volume : Measure X) volume := by
  have h (ij : UpperEntryPair n) : MeasurePreserving (fun z : ℂ => z * (p ij.1.2 : ℂ)) := by
    let e := LinearEquiv.smulOfNeZero ℂ ℂ (p ij.1.2 : ℂ) (p ij.1.2).ne_zero
    let L : ℂ ≃ₗᵢ[ℝ] ℂ :=
      { toLinearEquiv := e.restrictScalars ℝ
        norm_map' := fun z => by
          change ‖(p ij.1.2 : ℂ) * z‖ = ‖z‖
          rw [norm_mul, hp, one_mul] }
    convert L.measurePreserving using 1
    funext z
    change z * (p ij.1.2 : ℂ) = (p ij.1.2 : ℂ) * z
    exact mul_comm _ _
  exact volume_preserving_pi h

private theorem upperTriangularEntries_phaseColumns (a : Z) (p : Fin n → ℂˣ) (z : X) :
    upperTriangularEntries (fun j => a j * (p j : ℂ)) (phaseColumns p z) =
      upperTriangularEntries a z * (Iwasawa.diagonalUnits p).val := by
  ext i j
  rw [Iwasawa.diagonalUnits_val, Matrix.mul_diagonal]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [upperTriangularEntries, phaseColumns, hij]
  · simp [upperTriangularEntries]
  · simp [upperTriangularEntries, not_lt_of_gt hji, ne_of_gt hji]

private def logRadii (d : Z) : Y := fun j => Real.log ‖d j‖

/-- The square zeta kernel with the diagonal variable in multiplicative complex coordinates. -/
def multiplicativeKernel (ds : Fin n → ComplexCharacterData) (Φ : Mat → ℂ) (f : G → ℂ)
    (s : ℂ) (d : Z) (k : K) (z : X) : ℂ :=
  Φ (upperTriangularEntries d z * k.val.val) * f k.val *
    ∏ j, borelFactor (ds j).weight (2 * (s + (ds j).exponent)) (d j)

private theorem continuous_triangular_entries :
    Continuous (fun p : Z × X => upperTriangularEntries p.1 p.2) := by
  apply continuous_matrix
  intro i j
  by_cases hij : i < j
  · simp only [upperTriangularEntries, dite_eq_left hij]
    exact (continuous_apply (⟨(i, j), hij⟩ : UpperEntryPair n)).comp
      (continuous_snd : Continuous (Prod.snd : Z × X → X))
  · by_cases he : i = j
    · simp only [upperTriangularEntries, dite_eq_right hij, ite_eq_left he]
      exact (continuous_apply i).comp (continuous_fst : Continuous (Prod.fst : Z × X → Z))
    · simp only [upperTriangularEntries, dite_eq_right hij, ite_eq_right he, continuous_const]

private theorem continuous_multiplicativeKernel_slice (ds : Fin n → ComplexCharacterData)
    {Φ : Mat → ℂ} (hΦ : Continuous Φ) (f : G → ℂ) (s : ℂ) (d : Z) (k : K) :
    Continuous (multiplicativeKernel ds Φ f s d k) := by
  have h₀ : Continuous (fun z : X => (d, z)) := continuous_const.prodMk continuous_id
  have h : Continuous (upperTriangularEntries d) :=
    (continuous_triangular_entries (n := n)).comp h₀
  exact ((hΦ.comp (h.matrix_mul continuous_const)).mul continuous_const).mul continuous_const

private theorem integral_diagonalPhase (κ : Measure K) [κ.IsMulLeftInvariant]
    (ds : Fin n → ComplexCharacterData) {Φ : Mat → ℂ} (hΦ : Continuous Φ)
    {f : G → ℂ} (hf : f ∈ complexStandardModule n (List.ofFn ds)) (s : ℂ) (d : Z)
    (hd : ∀ j, d j ≠ 0) :
    (∫ k, (∫ z : X, multiplicativeKernel ds Φ f s d k z) ∂κ) =
      ∫ k, (∫ z : X, logarithmicKernel ds Φ f s (logRadii d) z k) ∂κ := by
  let u (j : Fin n) := Units.mk0 (d j) (hd j)
  let p (j : Fin n) := phaseUnit (u j)
  let t : K := ⟨Iwasawa.diagonalUnits p, diagonalUnits_phaseUnit_mem u⟩
  let d₀ (j : Fin n) : ℂ := (‖d j‖ : ℝ)
  have hp (j : Fin n) : ‖(p j : ℂ)‖ = 1 := norm_phaseUnit (u j)
  have hprod (j : Fin n) : d₀ j * (p j : ℂ) = d j := by
    change (‖d j‖ : ℂ) * (phaseUnit (u j) : ℂ) = d j
    rw [phaseUnit_val, mul_comm]
    exact div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hd j)))
  have hrad (j : Fin n) : (Real.exp (logRadii d j) : ℂ) = d₀ j := by
    rw [logRadii, Real.exp_log (norm_pos_iff.mpr (hd j))]
  have hw :
      (∏ j, borelFactor (ds j).weight (2 * (s + (ds j).exponent)) (d j)) =
        principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn ds)) p *
          ∏ j, Complex.exp (2 * (s + (ds j).exponent) * logRadii d j) := by
    rw [principalSeriesCharacter_ofFn, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    nth_rw 1 [← hprod j]
    rw [borelFactor_mul _ _ (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hd j))) (p j).ne_zero,
      borelFactor_of_norm_eq_one _ _ (hp j), borelFactor_of_norm_eq_one _ _ (hp j),
      ← show (Real.exp (logRadii d j) : ℂ) = (‖d j‖ : ℂ) from hrad j, borelFactor_exp]
    rw [mul_comm ((p j : ℂ) ^ (ds j).weight), mul_comm (2 * (s + (ds j).exponent))]
  have he (k : K) : f (t * k).val =
      principalSeriesCharacter ℂ n (complexPositionCharacter (List.ofFn ds)) p * f k.val := by
    change f (Iwasawa.diagonalUnits p * k.val) = _
    simpa only [OneMemClass.coe_one, mul_one] using hf.2 p 1 k.val
  have hk (k : K) (z : X) :
      multiplicativeKernel ds Φ f s d k (phaseColumns p z) =
        logarithmicKernel ds Φ f s (logRadii d) z (t * k) := by
    unfold multiplicativeKernel logarithmicKernel
    rw [hw, he]
    simp_rw [hrad]
    have hm : upperTriangularEntries d (phaseColumns p z) =
        upperTriangularEntries d₀ z * (Iwasawa.diagonalUnits p).val := by
      simpa only [hprod] using upperTriangularEntries_phaseColumns d₀ p z
    rw [hm, Matrix.mul_assoc]
    change Φ (upperTriangularEntries d₀ z * ((t * k).val.val)) * _ * _ = _
    ring
  have hpres := measurePreserving_phaseColumns p hp
  calc
    _ = ∫ k, (∫ z : X, multiplicativeKernel ds Φ f s d k (phaseColumns p z)) ∂κ := by
      apply integral_congr_ae
      filter_upwards with k
      let B := multiplicativeKernel ds Φ f s d k
      change (∫ z, B z) = ∫ z, B (phaseColumns p z)
      calc
        _ = ∫ z, B z ∂(volume : Measure X).map (phaseColumns p) := by
          rw [hpres.map_eq]
        _ = _ := integral_map hpres.measurable.aemeasurable
          (continuous_multiplicativeKernel_slice ds hΦ f s d k).aestronglyMeasurable
    _ = ∫ k, (∫ z : X, logarithmicKernel ds Φ f s (logRadii d) z (t * k)) ∂κ := by
      simp only [hk]
    _ = _ := (measurePreserving_mul_left κ t).integral_comp (measurableEmbedding_mulLeft t)
      (fun k => ∫ z : X, logarithmicKernel ds Φ f s (logRadii d) z k)

private theorem measurable_radialIntegral (κ : Measure K) [SFinite κ]
    (ds : Fin n → ComplexCharacterData) {Φ : Mat → ℂ} (hΦ : Continuous Φ)
    {f : G → ℂ} (hf : Continuous f) (s : ℂ) :
    StronglyMeasurable (fun y : Y => ∫ k, (∫ z : X, logarithmicKernel ds Φ f s y z k) ∂κ) := by
  let T := (Y × K) × X
  have hy (j : Fin n) : Continuous (fun p : T => p.1.1 j) :=
    (continuous_apply j).comp (continuous_fst.comp continuous_fst)
  have ha : Continuous (fun p : T => fun j : Fin n => (Real.exp (p.1.1 j) : ℂ)) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hy j))
  have hmat : Continuous (fun p : T =>
      upperTriangularEntries (fun j => (Real.exp (p.1.1 j) : ℂ)) p.2 * p.1.2.val.val) :=
    ((continuous_triangular_entries (n := n)).comp (ha.prodMk continuous_snd)).matrix_mul
      (Units.continuous_val.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hker : Continuous (fun p : T => logarithmicKernel ds Φ f s p.1.1 p.2 p.1.2) :=
    ((hΦ.comp hmat).mul (hf.comp (continuous_subtype_val.comp
      (continuous_snd.comp continuous_fst)))).mul
      (continuous_finsetProd _ fun j _ => Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp (hy j))))
  exact hker.stronglyMeasurable.integral_prod_right'.integral_prod_right'

/-- The complex square zeta integral uses the full complex diagonal with multiplicative
Lebesgue measure, with a fixed positive factor determined by the group and compact measures. -/
def ComplexSquareZetaPhaseStatement : Prop :=
  ∀ (μ : Measure G) (κ : Measure K), μ.IsHaarMeasure → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (ds : Fin n → ComplexCharacterData) (Φ : Mat → ℂ) (f : G → ℂ),
      Continuous Φ → f ∈ complexStandardModule n (List.ofFn ds) → ∀ s : ℂ,
        Integrable (zetaKernel Φ f s) μ →
        (∫ g, zetaKernel Φ f s g ∂μ) =
          (c : ℂ) * ∫ d : Z, (∫ k, ∫ z : X, multiplicativeKernel ds Φ f s d k z ∂volume ∂κ)
            ∂Measure.pi (fun _ : Fin n => multiplicativeComplexLebesgue)

theorem complexSquareZetaPhase : ComplexSquareZetaPhaseStatement (n := n) := by
  intro μ κ hμ hκ
  let : κ.IsHaarMeasure := hκ
  obtain ⟨c, hc, hpos⟩ := complexSquareZetaPositiveDiagonal μ κ hμ hκ
  let b := (Real.toNNReal (2 * Real.pi)) ^ n
  have hb : 0 < b := pow_pos (Real.toNNReal_pos.mpr (mul_pos two_pos Real.pi_pos)) _
  refine ⟨c / b, div_pos hc hb, fun ds Φ f hΦ hf s hI => ?_⟩
  let ρ : Measure Z := Measure.pi (fun _ : Fin n => multiplicativeComplexLebesgue)
  let F (y : Y) : ℂ := ∫ k, (∫ z : X, logarithmicKernel ds Φ f s y z k) ∂κ
  let B (a : Z) : ℂ := ∫ k, (∫ z : X, multiplicativeKernel ds Φ f s a k z) ∂κ
  have hB : (∫ d, B d ∂ρ) = (b : ℂ) * ∫ y, F y := by
    have hnonzero : ∀ᵐ d ∂ρ, ∀ j, d j ≠ 0 :=
      ae_all_iff.mpr fun j => Measure.ae_eval_ne (fun _ : Fin n => multiplicativeComplexLebesgue) j 0
    have hm : Measurable (logRadii (n := n)) :=
      measurable_pi_iff.mpr fun j => Real.measurable_log.comp (measurable_pi_apply j).norm
    have hF := measurable_radialIntegral κ ds hΦ hf.1.continuous s
    calc
      _ = ∫ d, F (logRadii d) ∂ρ := integral_congr_ae (hnonzero.mono
        (fun d hd => integral_diagonalPhase κ ds hΦ hf s d hd))
      _ = ∫ y, F y ∂ρ.map logRadii := (integral_map hm.aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by
        rw [show ρ.map logRadii = b • (volume : Measure Y) from map_log_norm_diagonal n,
          integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]
  rw [hpos ds Φ f hΦ hf s hI]
  change (c : ℂ) * (∫ y, F y) = ((c / b : ℝ≥0) : ℂ) * ∫ d, B d ∂ρ
  rw [hB, NNReal.coe_div, Complex.ofReal_div]
  field_simp [show (b : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr hb).ne']

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
