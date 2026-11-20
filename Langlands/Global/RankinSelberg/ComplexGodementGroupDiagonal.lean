import Langlands.Global.RankinSelberg.ComplexGodementTateReduction

/-! # The group-to-diagonal reduction of the complex Godement integral -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Manifold Matrix.Norms.Operator NNReal ENNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexLocalWhittakerGauge (logTorus)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance groupDiagonalGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) :=
  borel _
local instance groupDiagonalGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance groupDiagonalGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Y" => (Fin n → ℝ)
local notation "X" => (UpperEntryPair n → ℂ)
local notation "Z" => (Fin n → ℂ)

private def groupCoordinates (p : Y × (K × X)) : G :=
  p.2.1.val * ((upperEntryCoordinates n).symm p.2.2).val * logTorus p.1

private theorem measurable_groupCoordinates : Measurable (groupCoordinates (n := n)) :=
  ((measurable_subtype_coe.comp (measurable_fst.comp measurable_snd)).mul
    (measurable_subtype_coe.comp ((upperEntryCoordinates n).symm.measurable.comp
      (measurable_snd.comp measurable_snd)))).mul
    (ComplexLocalIwasawa.continuous_logTorus.measurable.comp measurable_fst)

private theorem exists_groupCoordinates_measure (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (κ : Measure K) [κ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ μ = c • ((volume : Measure Y).prod (κ.prod (volume : Measure X))).map
      groupCoordinates := by
  obtain ⟨c, hc, h⟩ := exists_rightIwasawa_entryMeasure μ κ
  refine ⟨c, hc, ?_⟩
  let e : (Y × X) × K → Y × (K × X) := Prod.map id Prod.swap ∘ MeasurableEquiv.prodAssoc
  have hE : MeasurePreserving e (((volume : Measure Y).prod (volume : Measure X)).prod κ)
      (volume.prod (κ.prod volume)) :=
    ((MeasurePreserving.id (volume : Measure Y)).prod
      (measurePreserving_swap (μ := (volume : Measure X)) (ν := κ))).comp
      (measurePreserving_prodAssoc volume volume κ)
  rw [← hE.map_eq, Measure.map_map measurable_groupCoordinates hE.measurable]
  exact h

private theorem scaleUpperEntries_neg_inverse (y : Y) (z : X) :
    scaleUpperEntries y (scaleUpperEntries (-y) z) = z := by
  funext ij
  change Real.exp (y ij.1.2) • (Real.exp (-y ij.1.2) • z ij) = z ij
  rw [smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]

private theorem measurable_scaleUpperEntries_joint :
    Measurable (fun p : Y × X => scaleUpperEntries p.1 p.2) := by
  apply Measurable.of_eval
  intro ij
  change Measurable (fun p : Y × X => Real.exp (p.1 ij.1.2) • p.2 ij)
  exact (Real.continuous_exp.measurable.comp ((measurable_pi_apply ij.1.2).comp measurable_fst)).smul
    ((measurable_pi_apply ij).comp measurable_snd)

private theorem measurable_jacobian : Measurable (fun y : Y => ((upperEntryJacobian y : ℝ) : ℂ)) := by
  apply Complex.continuous_ofReal.measurable.comp
  simp_rw [upperEntryJacobian_coe]
  exact Finset.measurable_prod _ fun j _ =>
    (((Real.continuous_exp.measurable.comp (measurable_pi_apply j)).pow_const 2).inv).pow_const j.val

private theorem jacobian_mul_groupKernel (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) {f : G → ℂ}
    (hf : f ∈ complexStandardModule n ds) (g : Langlands.GeneralLinear (n + 1) ℂ)
    (y : Y) (k : K) (x : X) :
    ((upperEntryJacobian y : ℝ) : ℂ) *
      godementSectionIntegrand d Φ f g (groupCoordinates (y, k, x)) =
      triangularGodementKernel d ds Φ f g k y (scaleUpperEntries y x) := by
  let a (j : Fin n) : ℂˣ :=
    Units.mk0 (Real.exp (y j) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))
  have h := godementSectionIntegrand_triangular d ds Φ hf g ((upperEntryCoordinates n).symm x) k y a
    (fun _ => rfl)
  rw [Homeomorph.apply_symm_apply] at h
  rw [triangularGodementKernel_eq_complexDiagonalKernel]
  exact h

private theorem measurable_triangularGodementKernel_ordered (d : ComplexCharacterData)
    (ds : List ComplexCharacterData) {Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ}
    (hΦ : Continuous Φ) {f : G → ℂ} (hf : f ∈ complexStandardModule n ds)
    (g : Langlands.GeneralLinear (n + 1) ℂ) :
    Measurable (fun p : Y × (K × X) => triangularGodementKernel d ds Φ f g p.2.1 p.1 p.2.2) := by
  let T := Y × (K × X)
  have hI : Measurable (godementSectionIntegrand d Φ f g) :=
    ((continuous_godementSectionIntegrand d hΦ hf.1.continuous).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hs : Measurable (fun p : T => scaleUpperEntries (-p.1) p.2.2) :=
    measurable_scaleUpperEntries_joint.comp (measurable_fst.neg.prodMk
      (measurable_snd.comp measurable_snd))
  have hq : Measurable (fun p : T => groupCoordinates (p.1, p.2.1, scaleUpperEntries (-p.1) p.2.2)) :=
    measurable_groupCoordinates.comp (measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hs))
  have h := (measurable_jacobian.comp (measurable_fst : Measurable (Prod.fst : T → Y))).mul
    (hI.comp hq)
  change Measurable (fun p : T => ((upperEntryJacobian p.1 : ℝ) : ℂ) *
    godementSectionIntegrand d Φ f g (groupCoordinates (p.1, p.2.1, scaleUpperEntries (-p.1) p.2.2))) at h
  have heq : (fun p : T => ((upperEntryJacobian p.1 : ℝ) : ℂ) *
      godementSectionIntegrand d Φ f g (groupCoordinates (p.1, p.2.1, scaleUpperEntries (-p.1) p.2.2))) =
      fun p => triangularGodementKernel d ds Φ f g p.2.1 p.1 p.2.2 := by
    funext p
    rw [jacobian_mul_groupKernel d ds Φ hf, scaleUpperEntries_neg_inverse]
  rwa [heq] at h

private theorem integrate_entry_scaling (y : Y) {I A : X → ℂ} (hI : Measurable I) (hA : Measurable A)
    (heq : ∀ x, ((upperEntryJacobian y : ℝ) : ℂ) * I x = A (scaleUpperEntries y x)) :
    (∫⁻ x, ‖I x‖ₑ) = (∫⁻ z, ‖A z‖ₑ) ∧ (∫ x, I x) = ∫ z, A z := by
  let c := upperEntryJacobian y
  let J : ℂ := (c : ℝ)
  have hc : 0 < c := upperEntryJacobian_pos y
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc.ne'
  have hJ0 : J ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr hc).ne'
  have hJnorm : ‖J‖ₑ = (c : ℝ≥0∞) := by
    simp only [J, enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal, coe_nnnorm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg c)]
  have hm : Measurable (scaleUpperEntries y) :=
    measurable_scaleUpperEntries_joint.comp (measurable_const.prodMk measurable_id)
  constructor
  · apply (ENNReal.mul_left_inj hc0 ENNReal.coe_ne_top).mp
    calc
      _ = ∫⁻ x, ‖J * I x‖ₑ := by
        simp_rw [enorm_mul, hJnorm, lintegral_const_mul _ hI.enorm]
        exact mul_comm _ _
      _ = ∫⁻ x, ‖A (scaleUpperEntries y x)‖ₑ := lintegral_congr fun x => congrArg enorm (heq x)
      _ = ∫⁻ z, ‖A z‖ₑ ∂(volume : Measure X).map (scaleUpperEntries y) :=
        (lintegral_map hA.enorm hm).symm
      _ = _ := by
        rw [map_scaleUpperEntries, lintegral_smul_measure]
        exact mul_comm _ _
  · apply mul_left_cancel₀ hJ0
    calc
      _ = ∫ x, J * I x := (integral_const_mul _ _).symm
      _ = ∫ x, A (scaleUpperEntries y x) := integral_congr_ae (Filter.Eventually.of_forall heq)
      _ = ∫ z, A z ∂(volume : Measure X).map (scaleUpperEntries y) :=
        (integral_map hm.aemeasurable hA.aestronglyMeasurable).symm
      _ = _ := by
        rw [map_scaleUpperEntries, integral_smul_nnreal_measure]
        simp only [NNReal.smul_def, Complex.real_smul, J]
        rfl

/-- The complex Godement group integral reduces to its multiplicative diagonal integral with
fixed measure factor. The two kernels have equivalent absolute integrability. -/
def ComplexGodementGroupDiagonalStatement : Prop :=
  ∀ (μ : Measure G) (κ : Measure K), μ.IsHaarMeasure → μ.IsMulRightInvariant → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (d : ComplexCharacterData) (ds : List ComplexCharacterData)
      (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (f : G → ℂ),
      Continuous Φ → f ∈ complexStandardModule n ds →
      ∀ g : Langlands.GeneralLinear (n + 1) ℂ,
        let ρ := Measure.pi (fun _ : Fin n => multiplicativeComplexLebesgue)
        let η := κ.prod (volume : Measure X)
        let I := godementSectionIntegrand d Φ f g
        let B (p : Z × (K × X)) := multiplicativeDiagonalKernel d ds Φ f g p.1 p.2.1 p.2.2
        (Integrable I μ ↔ Integrable B (ρ.prod η)) ∧
          (Integrable I μ → (∫ h, I h ∂μ) = (c : ℂ) * ∫ p, B p ∂ρ.prod η)

set_option maxHeartbeats 600000 in
theorem complexGodementGroupDiagonal : ComplexGodementGroupDiagonalStatement (n := n) := by
  intro μ κ hμ hright hκ
  let : μ.IsHaarMeasure := hμ
  let : μ.IsMulRightInvariant := hright
  let : κ.IsHaarMeasure := hκ
  have : κ.IsMulRightInvariant := Langlands.CompactFactorization.isMulRightInvariant_of_compactSpace κ
  obtain ⟨c, hc, hq⟩ := exists_groupCoordinates_measure μ κ
  let b := (Real.toNNReal (2 * Real.pi)) ^ n
  have hb : 0 < b := pow_pos (Real.toNNReal_pos.mpr (mul_pos two_pos Real.pi_pos)) n
  refine ⟨c / b, div_pos hc hb, ?_⟩
  intro d ds Φ f hΦ hf g ρ η I B
  let A (p : Y × (K × X)) := triangularGodementKernel d ds Φ f g p.2.1 p.1 p.2.2
  let Q (p : Y × (K × X)) := I (groupCoordinates p)
  let ν := (volume : Measure Y).prod η
  change μ = c • ν.map groupCoordinates at hq
  have hAm : Measurable A := measurable_triangularGodementKernel_ordered d ds hΦ hf g
  have hIm : Measurable I :=
    ((continuous_godementSectionIntegrand d hΦ hf.1.continuous).comp
      (continuous_const.prodMk continuous_id)).measurable
  have hQm : Measurable Q := hIm.comp measurable_groupCoordinates
  have hA₁ (y : Y) : Measurable (fun p : K × X => A (y, p)) := hAm.comp (measurable_const.prodMk measurable_id)
  have hQ₁ (y : Y) : Measurable (fun p : K × X => Q (y, p)) := hQm.comp (measurable_const.prodMk measurable_id)
  have hswap (y : Y) (k : K) := integrate_entry_scaling y
    ((hQ₁ y).comp (measurable_const.prodMk measurable_id) : Measurable (fun x : X => Q (y, k, x)))
    ((hA₁ y).comp (measurable_const.prodMk measurable_id) : Measurable (fun x : X => A (y, k, x)))
    (jacobian_mul_groupKernel d ds Φ hf g y k)
  have hnorm : (∫⁻ h, ‖I h‖ₑ ∂μ) = (c : ℝ≥0∞) * ∫⁻ p, ‖A p‖ₑ ∂ν := by
    rw [hq, lintegral_smul_measure, lintegral_map hIm.enorm measurable_groupCoordinates]
    change (c : ℝ≥0∞) * (∫⁻ p, ‖Q p‖ₑ ∂ν) = _
    congr 1
    rw [lintegral_prod _ hQm.enorm.aemeasurable, lintegral_prod _ hAm.enorm.aemeasurable]
    apply lintegral_congr
    intro y
    rw [lintegral_prod _ (hQ₁ y).enorm.aemeasurable, lintegral_prod _ (hA₁ y).enorm.aemeasurable]
    exact lintegral_congr fun k => (hswap y k).1
  have hc0 : (c : ℝ≥0∞) ≠ 0 := ENNReal.coe_ne_zero.mpr hc.ne'
  have hPositive : Integrable I μ ↔ Integrable A ν := by
    simp only [Integrable, hIm.aestronglyMeasurable, hAm.aestronglyMeasurable, true_and,
      hasFiniteIntegral_iff_enorm, hnorm]
    simp [lt_top_iff_ne_top, ENNReal.mul_eq_top, hc0]
  obtain ⟨hDiag, hInt⟩ := complexGodementMultiplicativeDiagonal κ d ds hΦ hf g
  refine ⟨hPositive.trans hDiag.symm, fun hI => ?_⟩
  have hA := hPositive.mp hI
  have hi : Integrable I (ν.map groupCoordinates) := by
    rw [hq] at hI
    exact (integrable_smul_measure hc0 ENNReal.coe_ne_top).mp hI
  have hQ : Integrable Q ν :=
    (integrable_map_measure hIm.aestronglyMeasurable measurable_groupCoordinates.aemeasurable).mp hi
  have hBochner : (∫ p, Q p ∂ν) = ∫ p, A p ∂ν := by
    rw [integral_prod _ hQ, integral_prod _ hA]
    apply integral_congr_ae
    filter_upwards [hQ.prod_right_ae, hA.prod_right_ae] with y hyQ hyA
    rw [integral_prod _ hyQ, integral_prod _ hyA]
    apply integral_congr_ae
    filter_upwards [] with k
    exact (hswap y k).2
  have hbℂ : (b : ℂ) = ((2 * Real.pi : ℝ) : ℂ) ^ n := by
    simp [b, Real.coe_toNNReal _ (mul_nonneg two_pos.le Real.pi_pos.le)]
  rw [hq, integral_smul_nnreal_measure, integral_map measurable_groupCoordinates.aemeasurable
    hIm.aestronglyMeasurable]
  change c • (∫ p, Q p ∂ν) = _
  rw [hBochner, hInt hA, ← hbℂ]
  simp only [NNReal.smul_def, Complex.real_smul, NNReal.coe_div, Complex.ofReal_div]
  have hb0 : (b : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (NNReal.coe_pos.mpr hb).ne'
  field_simp
  rfl

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
