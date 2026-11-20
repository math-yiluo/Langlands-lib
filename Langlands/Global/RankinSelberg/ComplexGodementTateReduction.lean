import Langlands.Global.RankinSelberg.ComplexGodementCompact
import Langlands.Global.RankinSelberg.ComplexGodementDiagonalPhase
import Langlands.Global.RankinSelberg.ComplexGodementLogRadius
import Langlands.Global.RankinSelberg.ComplexGodementTateWeight

/-! # The complex multiplicative diagonal integral of a Godement section -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Manifold Matrix.Norms.Operator NNReal ENNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Archimedean.ComplexGramFormula (phaseUnit phaseUnit_val norm_phaseUnit)

set_option autoImplicit false

local instance diagonalTateGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) :=
  borel _
local instance diagonalTateGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance diagonalTateGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology
local instance diagonalTateUnitsMeasurable : MeasurableSpace ℂˣ := borel _
local instance diagonalTateUnitsBorel : BorelSpace ℂˣ := ⟨rfl⟩
local instance diagonalTateUnitsSecondCountable : SecondCountableTopology ℂˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Y" => (Fin n → ℝ)
local notation "Z" => (Fin n → ℂ)
local notation "X" => (UpperEntryPair n → ℂ)

private def totalUnit (a : ℂ) : ℂˣ := if h : a = 0 then 1 else Units.mk0 a h

private def positiveUnit (y : ℝ) : ℂˣ :=
  Units.mk0 (Real.exp y : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero y))

private theorem measurable_totalUnit : Measurable totalUnit := by
  have he : Topology.IsOpenEmbedding (Units.val : ℂˣ → ℂ) := IsOpenUnits.isOpenEmbedding_unitsVal
  apply he.measurableEmbedding.measurable_comp_iff.mp
  have h : (Units.val : ℂˣ → ℂ) ∘ totalUnit = fun a : ℂ => if a = 0 then 1 else a := by
    funext a
    by_cases ha : a = 0 <;> simp [totalUnit, ha]
  rw [h]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const measurable_id

private theorem continuous_positiveUnit : Continuous positiveUnit := by
  rw [Units.continuous_iff]
  constructor
  · exact Complex.continuous_ofReal.comp Real.continuous_exp
  · change Continuous fun y : ℝ => (positiveUnit y)⁻¹.val
    simp only [Units.val_inv_eq_inv_val]
    exact (Complex.continuous_ofReal.comp Real.continuous_exp).inv₀
      fun y => (positiveUnit y).ne_zero

private theorem totalUnit_phase (z : ℂ) : totalUnit z =
    phaseUnit (totalUnit z) * positiveUnit (Real.log ‖z‖) := by
  apply Units.ext
  rw [Units.val_mul, phaseUnit_val]
  by_cases hz : z = 0
  · simp [hz, totalUnit, positiveUnit]
  · have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hne : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm.ne'
    simp only [totalUnit, dite_eq_right hz, Units.val_mk0, positiveUnit, Real.exp_log hnorm]
    exact (div_mul_cancel₀ _ hne).symm

private theorem continuous_positionCharacter (ds : List ComplexCharacterData) :
    ∀ j : ℕ, Continuous (complexPositionCharacter ds j) := by
  induction ds with
  | nil => intro j; exact continuous_const
  | cons d ds ih =>
    intro j
    cases j with
    | zero => exact Units.continuous_val.comp d.character.continuous
    | succ j => exact ih j

private theorem continuous_diagonalTateWeight (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) : Continuous (diagonalTateWeight (n := n) d ds) := by
  unfold diagonalTateWeight
  apply continuous_finsetProd
  intro j _
  have hj : Continuous (fun a : Fin n → ℂˣ => a j) := continuous_apply j
  have hfirst : Continuous fun a : Fin n → ℂˣ => characterWeight d 1 (a j) :=
    (continuous_characterWeight d 1).comp hj
  have hsecond : Continuous fun a : Fin n → ℂˣ => complexPositionCharacter ds j (a j)⁻¹ :=
    (continuous_positionCharacter ds j).comp hj.inv
  have he : (fun a : Fin n → ℂˣ => characterWeight d 1 (a j) *
      complexPositionCharacter ds j (a j)⁻¹) = fun a =>
      ((d.character (a j) : ℂ) * complexPositionCharacter ds j (a j)⁻¹) * normPower 1 (a j) := by
    funext a
    change ((d.character (a j) : ℂ) * normPower 1 (a j)) *
      complexPositionCharacter ds j (a j)⁻¹ = _
    ring
  rw [← he]
  exact hfirst.mul hsecond

private theorem continuous_complexDiagonalKernel_joint (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ}
    (hΦ : Continuous Φ) {f : G → ℂ} (hf : Continuous f) (g : Langlands.GeneralLinear (n + 1) ℂ) :
    Continuous (fun p : (Fin n → ℂˣ) × (K × X) => complexDiagonalKernel d ds Φ f g p.1 p.2.1 p.2.2) := by
  let P := (Fin n → ℂˣ) × (K × X)
  have hk : Continuous (fun p : P => p.2.1.val) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hB : Continuous (fun p : P => upperTriangularEntries (fun j => (p.1 j : ℂ)) p.2.2) := by
    apply continuous_matrix
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp only [upperTriangularEntries, dite_eq_left hij]
      exact (continuous_apply (⟨(i, j), hij⟩ : UpperEntryPair n)).comp
        (continuous_snd.comp continuous_snd)
    · simp only [upperTriangularEntries, lt_irrefl, dite_false, ite_true]
      exact Units.continuous_val.comp ((continuous_apply i).comp continuous_fst)
    · simp only [upperTriangularEntries, not_lt_of_gt hji, dite_false, ne_of_gt hji, ite_false]
      exact continuous_const
  have hT : Continuous (fun p : P => p.2.1.val.val *
      upperTriangularEntries (fun j => (p.1 j : ℂ)) p.2.2 * trailingRows g.val) :=
    ((Units.continuous_val.comp hk).matrix_mul hB).matrix_mul continuous_const
  have hχ : Continuous (fun p : P => (d.character (determinant p.2.1.val) : ℂ)) :=
    (Units.continuous_val.comp d.character.continuous).comp
    (determinantContinuous.continuous.comp hk)
  exact ((hΦ.comp hT).mul ((hf.comp hk.inv).mul hχ)).mul
    ((continuous_diagonalTateWeight d ds).comp continuous_fst)

/-- The kernel in complex additive coordinates on the diagonals, to be integrated with
multiplicative complex Lebesgue measure in those coordinates. -/
def multiplicativeDiagonalKernel (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (f : G → ℂ)
    (g : Langlands.GeneralLinear (n + 1) ℂ) (a : Z) (k : K) (z : X) : ℂ :=
  complexDiagonalKernel d ds Φ f g (fun j => totalUnit (a j)) k z

set_option maxHeartbeats 600000 in
private theorem measurable_multiplicativeKernel (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ}
    (hΦ : Continuous Φ) {f : G → ℂ} (hf : Continuous f) (g : Langlands.GeneralLinear (n + 1) ℂ) :
    Measurable (fun p : Z × (K × X) => multiplicativeDiagonalKernel d ds Φ f g p.1 p.2.1 p.2.2) := by
  have : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology (K : Set G))
  have : BorelSpace K := inferInstanceAs (BorelSpace (K : Set G))
  have : BorelSpace (K × X) := Prod.borelSpace
  have : BorelSpace ((Fin n → ℂˣ) × (K × X)) := Prod.borelSpace
  have h : Measurable (fun a : Z => fun j => totalUnit (a j)) :=
    Measurable.of_eval fun j => measurable_totalUnit.comp (measurable_pi_apply j)
  have hp : Measurable (fun p : Z × (K × X) => (fun j => totalUnit (p.1 j), p.2)) :=
    (h.comp measurable_fst).prodMk measurable_snd
  have hcomp := (continuous_complexDiagonalKernel_joint d ds hΦ hf g).measurable.comp hp
  simpa only [Function.comp_def, multiplicativeDiagonalKernel] using hcomp

private theorem continuous_triangularGodementKernel_joint (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ}
    (hΦ : Continuous Φ) {f : G → ℂ} (hf : Continuous f) (g : Langlands.GeneralLinear (n + 1) ℂ) :
    Continuous (fun p : Y × (K × X) => triangularGodementKernel d ds Φ f g p.2.1 p.1 p.2.2) := by
  have h : Continuous (fun y : Y => fun j => positiveUnit (y j)) :=
    continuous_pi fun j => continuous_positiveUnit.comp (continuous_apply j)
  have hp : Continuous (fun p : Y × (K × X) => (fun j => positiveUnit (p.1 j), p.2)) :=
    (h.comp continuous_fst).prodMk continuous_snd
  simpa only [Function.comp_def, triangularGodementKernel_eq_complexDiagonalKernel, positiveUnit] using
    (continuous_complexDiagonalKernel_joint d ds hΦ hf g).comp hp

private def logRadii (a : Z) : Y := fun j => Real.log ‖a j‖

private theorem measurable_logRadii : Measurable (logRadii (n := n)) :=
  Measurable.of_eval fun j => Real.measurable_log.comp (measurable_pi_apply j).norm

private theorem absoluteDiagonalKernel_radial (κ : Measure K) [κ.IsMulRightInvariant]
    (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ} (hΦ : Continuous Φ)
    {f : G → ℂ} (hf : f ∈ complexStandardModule n ds)
    (g : Langlands.GeneralLinear (n + 1) ℂ) (a : Z) :
    (∫⁻ k, (∫⁻ z, ‖multiplicativeDiagonalKernel d ds Φ f g a k z‖ₑ) ∂κ) =
      ∫⁻ k, (∫⁻ z, ‖triangularGodementKernel d ds Φ f g k (logRadii a) z‖ₑ) ∂κ := by
  let p (j : Fin n) := phaseUnit (totalUnit (a j))
  let b (j : Fin n) := positiveUnit (logRadii a j)
  have h : (fun j => totalUnit (a j)) = p * b := funext fun j => totalUnit_phase (a j)
  unfold multiplicativeDiagonalKernel
  rw [h]
  exact lintegral_enorm_complexDiagonalKernel_phase κ d ds hΦ hf g p b
    (fun j => norm_phaseUnit (totalUnit (a j)))

private theorem integralDiagonalKernel_radial (κ : Measure K) [κ.IsMulRightInvariant]
    (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ} (hΦ : Continuous Φ)
    {f : G → ℂ} (hf : f ∈ complexStandardModule n ds)
    (g : Langlands.GeneralLinear (n + 1) ℂ) (a : Z) :
    (∫ k, (∫ z, multiplicativeDiagonalKernel d ds Φ f g a k z) ∂κ) =
      ∫ k, (∫ z, triangularGodementKernel d ds Φ f g k (logRadii a) z) ∂κ := by
  let p (j : Fin n) := phaseUnit (totalUnit (a j))
  let b (j : Fin n) := positiveUnit (logRadii a j)
  have h : (fun j => totalUnit (a j)) = p * b := funext fun j => totalUnit_phase (a j)
  unfold multiplicativeDiagonalKernel
  rw [h]
  exact integral_complexDiagonalKernel_phase κ d ds hΦ hf g p b
    (fun j => norm_phaseUnit (totalUnit (a j)))

set_option backward.isDefEq.respectTransparency false in
/-- The triangular integral can be taken over complex multiplicative diagonals. Absolute
integrability is equivalent in the two forms, and the integral in complex coordinates has the
factor `(2π)^n` relative to the integral in logarithmic positive coordinates. -/
theorem complexGodementMultiplicativeDiagonal (κ : Measure K) [SFinite κ]
    [κ.IsMulRightInvariant] (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ} (hΦ : Continuous Φ)
    {f : G → ℂ} (hf : f ∈ complexStandardModule n ds) (g : Langlands.GeneralLinear (n + 1) ℂ) :
    let ρ := Measure.pi (fun _ : Fin n => multiplicativeComplexLebesgue)
    let η := κ.prod (volume : Measure X)
    let A (p : Y × (K × X)) := triangularGodementKernel d ds Φ f g p.2.1 p.1 p.2.2
    let B (p : Z × (K × X)) := multiplicativeDiagonalKernel d ds Φ f g p.1 p.2.1 p.2.2
    (Integrable B (ρ.prod η) ↔ Integrable A (volume.prod η)) ∧
      (Integrable A (volume.prod η) →
        (∫ p, B p ∂ρ.prod η) = ((2 * Real.pi : ℝ) : ℂ) ^ n * ∫ p, A p ∂volume.prod η) := by
  intro ρ η A B
  let c := (Real.toNNReal (2 * Real.pi)) ^ n
  have hc : 0 < c := pow_pos (Real.toNNReal_pos.mpr (mul_pos two_pos Real.pi_pos)) n
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc.ne'
  have hmap : ρ.map logRadii = c • (volume : Measure Y) := map_log_norm_diagonal n
  have : SecondCountableTopology K := inferInstanceAs (SecondCountableTopology (K : Set G))
  have : BorelSpace K := inferInstanceAs (BorelSpace (K : Set G))
  have : BorelSpace (K × X) := Prod.borelSpace
  have : BorelSpace (Y × (K × X)) := Prod.borelSpace
  have hfC : Continuous f := hf.1.continuous
  have hAm : Measurable A :=
    (continuous_triangularGodementKernel_joint d ds hΦ hfC g).measurable
  have hBm : Measurable B := measurable_multiplicativeKernel d ds hΦ hfC g
  have hBslice (a : Z) : Measurable (fun p : K × X => B (a, p)) :=
    hBm.comp (measurable_const.prodMk measurable_id)
  have hAslice (y : Y) : Measurable (fun p : K × X => A (y, p)) :=
    hAm.comp (measurable_const.prodMk measurable_id)
  have hnorm (a : Z) : (∫⁻ p, ‖B (a, p)‖ₑ ∂η) =
      ∫⁻ p, ‖A (logRadii a, p)‖ₑ ∂η := by
    rw [lintegral_prod _ (hBslice a).enorm.aemeasurable,
      lintegral_prod _ (hAslice (logRadii a)).enorm.aemeasurable]
    exact absoluteDiagonalKernel_radial κ d ds hΦ hf g a
  have hnormTotal : (∫⁻ p, ‖B p‖ₑ ∂ρ.prod η) = (c : ℝ≥0∞) *
      ∫⁻ p, ‖A p‖ₑ ∂volume.prod η := by
    let H (y : Y) := ∫⁻ p, ‖A (y, p)‖ₑ ∂η
    have hH : Measurable H := hAm.enorm.lintegral_prod_right'
    calc
      _ = ∫⁻ a, (∫⁻ p, ‖B (a, p)‖ₑ ∂η) ∂ρ := lintegral_prod _ hBm.enorm.aemeasurable
      _ = ∫⁻ a, H (logRadii a) ∂ρ := lintegral_congr hnorm
      _ = ∫⁻ y, H y ∂ρ.map logRadii := (lintegral_map hH measurable_logRadii).symm
      _ = _ := by
        rw [hmap, lintegral_smul_measure, lintegral_prod _ hAm.enorm.aemeasurable]
        rfl
  have hIff : Integrable B (ρ.prod η) ↔ Integrable A (volume.prod η) := by
    simp only [Integrable, hAm.aestronglyMeasurable, hBm.aestronglyMeasurable, true_and,
      hasFiniteIntegral_iff_enorm, hnormTotal]
    simp [lt_top_iff_ne_top, ENNReal.mul_eq_top, hc0]
  refine ⟨hIff, fun hAi => ?_⟩
  have hBi := hIff.mpr hAi
  have hQ : QuasiMeasurePreserving logRadii ρ (volume : Measure Y) := by
    refine ⟨measurable_logRadii, ?_⟩
    rw [hmap]
    exact Measure.smul_absolutelyContinuous
  let H (y : Y) := ∫ p, A (y, p) ∂η
  have hH : StronglyMeasurable H := hAm.stronglyMeasurable.integral_prod_right'
  have hcℂ : (c : ℂ) = ((2 * Real.pi : ℝ) : ℂ) ^ n := by
    simp [c, Real.coe_toNNReal _ (mul_nonneg two_pos.le Real.pi_pos.le)]
  calc
    _ = ∫ a, (∫ p, B (a, p) ∂η) ∂ρ := integral_prod _ hBi
    _ = ∫ a, H (logRadii a) ∂ρ := by
      apply integral_congr_ae
      filter_upwards [hBi.prod_right_ae, hQ.ae hAi.prod_right_ae] with a ha ha'
      change (∫ p, B (a, p) ∂η) = ∫ p, A (logRadii a, p) ∂η
      rw [integral_prod _ ha, integral_prod _ ha']
      exact integralDiagonalKernel_radial κ d ds hΦ hf g a
    _ = ∫ y, H y ∂ρ.map logRadii :=
      (integral_map measurable_logRadii.aemeasurable hH.aestronglyMeasurable).symm
    _ = _ := by
      rw [hmap, integral_smul_nnreal_measure, integral_prod _ hAi, ← hcℂ]
      simp only [NNReal.smul_def, Complex.real_smul]
      rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
