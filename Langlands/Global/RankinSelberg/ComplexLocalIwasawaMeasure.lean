import Langlands.Global.RankinSelberg.ComplexLocalIwasawa
import Langlands.Global.RankinSelberg.RealIwasawaMeasure

/-! # The toral marginal of a compatible complex unipotent quotient measure -/

noncomputable section
open MeasureTheory
open scoped CompactlySupported ENNReal NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel ArchimedeanLocal.archimedeanComplexQMeasurable
  ArchimedeanLocal.archimedeanComplexQBorel

namespace ComplexLocalIwasawa

open ArchimedeanLocal
open Langlands.QuotientIntegration (quotientAverage quotientAverage_mk)
open ComplexLocalWhittakerGauge (logTorus)

variable {n : ℕ}

local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ

private theorem isClosed_unipotent : IsClosed (N : Set G) := by
  have hv : Continuous (Units.val : G → Mat) := Units.continuous_val
  have he : (N : Set G) =
      {g : G | g.val.IsUpperTriangular} ∩ ⋂ i : Fin n, {g : G | g.val i i = 1} := by
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact Iff.rfl
  rw [he]
  exact (isClosed_setOfPred_blockTriangular.preimage hv).inter
    (isClosed_iInter fun i => isClosed_eq ((continuous_apply_apply i i).comp hv) continuous_const)

private instance : LocallyCompactSpace Mat :=
  inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))

private instance : LocallyCompactSpace G :=
  inferInstanceAs (LocallyCompactSpace Matˣ)

private instance : LocallyCompactSpace N :=
  isClosed_unipotent.locallyCompactSpace

private instance : SecondCountableTopology Mat :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))

private instance : SecondCountableTopology G := by
  have : SecondCountableTopology Matᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

private instance : SecondCountableTopology N :=
  TopologicalSpace.Subtype.secondCountableTopology (N : Set G)

private theorem exists_bump :
    ∃ β : N → ℝ, Continuous β ∧ HasCompactSupport β ∧ (∀ u, 0 ≤ β u) ∧ β 1 = 1 := by
  obtain ⟨f, hf1, -, hfc, hf01⟩ := exists_continuous_one_zero_of_isCompact
    (isCompact_singleton (x := (1 : N))) isClosed_empty (Set.disjoint_empty _)
  exact ⟨f, f.continuous, hfc, fun u => (hf01 u).1, hf1 (Set.mem_singleton _)⟩

private def conjTorusHomeomorph (z : Fin n → ℝ) : N ≃ₜ N where
  toFun := conjTorus z
  invFun := conjTorus (-z)
  left_inv := conjTorus_neg z
  right_inv u := by simpa only [neg_neg] using conjTorus_neg (-z) u
  continuous_toFun := continuous_conjTorus z
  continuous_invFun := continuous_conjTorus (-z)

private theorem hasCompactSupport_lift {φ : (Fin n → ℝ) → ℝ} {β : N → ℝ}
    (hφ : HasCompactSupport φ) (hβ : HasCompactSupport β) :
    HasCompactSupport fun g : G => φ (alpha g) * β (npart g) := by
  refine HasCompactSupport.intro
    ((hβ.isCompact.prod (hφ.isCompact.prod isCompact_univ)).image
      (iwasawaHomeomorph n).continuous) ?_
  intro g hg
  by_contra hne
  exact hg ⟨(npart g, alpha g, kpart g),
    ⟨subset_tsupport _ (right_ne_zero_of_mul hne),
      subset_tsupport _ (left_ne_zero_of_mul hne), Set.mem_univ _⟩,
    npart_mul_logTorus_mul_kpart g⟩

section Weil

variable {t : ℕ}

local notation "GC" => Langlands.GeneralLinear (t + 1) ℂ
local notation "NC" => Langlands.GeneralLinear.upperUnipotent (t + 1) ℂ

variable (D : ComplexQuotientMeasureData t)

local notation "μG" => D.groupHaar
local notation "μN" => D.unipotentHaar
local notation "ν" => D.measure

private theorem quotientAverage_lift (φ : (Fin (t + 1) → ℝ) → ℝ) (β : NC → ℝ) :
    letI := D.unipotentHaar_rightInvariant
    quotientAverage NC μN (fun g => ((φ (alpha g) * β (npart g) : ℝ) : ℂ)) =
      fun q => ((φ (alphaQ q) * ∫ h, β h ∂μN : ℝ) : ℂ) := by
  have := D.unipotentHaar_rightInvariant
  funext q
  induction q using Quotient.inductionOn with
  | h g =>
    rw [quotientAverage_mk NC μN _ g, alphaQ_mk]
    simp_rw [alpha_unipotent_mul, npart_unipotent_mul]
    rw [integral_complex_ofReal, integral_const_mul,
      integral_mul_right_eq_self (μ := μN) (fun h => β h) (npart g)]

private theorem weil_lift
    {φ : (Fin (t + 1) → ℝ) → ℝ} {β : NC → ℝ} (hφc : Continuous φ)
    (hφ : HasCompactSupport φ) (hβc : Continuous β) (hβ : HasCompactSupport β) :
    (∫ q, φ (alphaQ q) ∂ν) * ∫ h, β h ∂μN = ∫ g, φ (alpha g) * β (npart g) ∂μG := by
  have := D.unipotentHaar_rightInvariant
  have hc := (hφc.comp continuous_alpha).mul (hβc.comp continuous_npart)
  have hf := D.compatible.integral_formula (fun g => ((φ (alpha g) * β (npart g) : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp hc) ((hasCompactSupport_lift hφ hβ).comp_left Complex.ofReal_zero)
  rw [quotientAverage_lift D] at hf
  simp only [integral_complex_ofReal] at hf
  have h := Complex.ofReal_injective hf
  rwa [integral_mul_const] at h

private theorem weil_translate
    {φ : (Fin (t + 1) → ℝ) → ℝ} {β : NC → ℝ} (hφc : Continuous φ)
    (hφ : HasCompactSupport φ) (hβc : Continuous β) (hβ : HasCompactSupport β)
    (z : Fin (t + 1) → ℝ) :
    (∫ q, φ (z + alphaQ q) ∂ν) * (∫ h, β (conjTorus z h) ∂μN) =
      (∫ q, φ (alphaQ q) ∂ν) * ∫ h, β h ∂μN := by
  have := D.groupHaar_isHaar
  have hφz : HasCompactSupport fun x => φ (z + x) :=
    hφ.comp_homeomorph (Homeomorph.addLeft z)
  have hβz : HasCompactSupport fun h => β (conjTorus z h) :=
    hβ.comp_homeomorph (conjTorusHomeomorph z)
  have h₁ := weil_lift D (φ := fun x => φ (z + x)) (β := fun h => β (conjTorus z h))
    (hφc.comp (continuous_const.add continuous_id)) hφz
    (hβc.comp (continuous_conjTorus z)) hβz
  have h₂ := weil_lift D hφc hφ hβc hβ
  rw [h₁, h₂, ← integral_mul_left_eq_self (μ := μG)
    (fun g => φ (alpha g) * β (npart g)) (logTorus z)]
  simp_rw [alpha_torus_mul, npart_torus_mul]

private theorem exists_quasiInvariant :
    ∃ e : (Fin (t + 1) → ℝ) → ℝ, (∀ z, 0 < e z) ∧ ∀ φ : (Fin (t + 1) → ℝ) → ℝ, Continuous φ →
      HasCompactSupport φ →
        ∀ z, ∫ x, φ (z + x) ∂(D.measure.map alphaQ) =
          e z * ∫ x, φ x ∂(D.measure.map alphaQ) := by
  have := D.unipotentHaar_isHaar
  obtain ⟨β, hβc, hβ, hβ0, hβ1⟩ := exists_bump (n := t + 1)
  have hc (z : Fin (t + 1) → ℝ) : 0 < ∫ h, β (conjTorus z h) ∂μN :=
    (hβc.comp (continuous_conjTorus z)).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (hβ.comp_homeomorph (conjTorusHomeomorph z)) (fun h => hβ0 _) (x := 1)
      (by simp only [map_one, hβ1]; exact one_ne_zero)
  have hc0 : 0 < ∫ h, β h ∂μN :=
    hβc.integral_pos_of_hasCompactSupport_nonneg_nonzero hβ hβ0 (x := 1)
      (by rw [hβ1]; exact one_ne_zero)
  refine ⟨fun z => (∫ h, β h ∂μN) / ∫ h, β (conjTorus z h) ∂μN,
    fun z => div_pos hc0 (hc z), ?_⟩
  intro φ hφc hφ z
  have hw := weil_translate D hφc hφ hβc hβ z
  have hα : Measurable (alphaQ (n := t + 1)) := continuous_alphaQ.measurable
  have hz : ∫ x, φ (z + x) ∂(D.measure.map alphaQ) = ∫ q, φ (z + alphaQ q) ∂ν :=
    integral_map hα.aemeasurable (hφc.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  rw [hz, integral_map hα.aemeasurable hφc.aestronglyMeasurable]
  rw [eq_comm, div_mul_eq_mul_div, div_eq_iff (hc z).ne', hw]
  ring

theorem exists_lintegral_alphaQ :
    ∃ (κ : ℝ≥0) (L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ), ∀ B : (Fin (t + 1) → ℝ) → ℝ≥0∞, Measurable B →
      ∫⁻ q, B (alphaQ q) ∂ν = (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x := by
  have := D.unipotentHaar_rightInvariant
  have := D.compatible.regular
  have hα : Measurable (alphaQ (n := t + 1)) := continuous_alphaQ.measurable
  have : IsFiniteMeasureOnCompacts (D.measure.map alphaQ) := ⟨fun C hC => by
    rw [Measure.map_apply hα hC.measurableSet]
    exact (isCompact_alphaQ_preimage hC).measure_lt_top⟩
  obtain ⟨e, he, hq⟩ := exists_quasiInvariant D
  have hρ : D.measure.map alphaQ ≠ 0 := by
    intro h
    apply D.compatible.nonzero
    rwa [Measure.map_eq_zero_iff hα.aemeasurable] at h
  obtain ⟨L, hL⟩ := RealIwasawa.exists_linear_of_quasiInvariant (D.measure.map alphaQ) hρ e he hq
  have hL' (φ : (Fin (t + 1) → ℝ) → ℝ) (hφc : Continuous φ) (hφ : HasCompactSupport φ)
      (z : Fin (t + 1) → ℝ) :
      ∫ x, φ (z + x) ∂(D.measure.map alphaQ) =
        Real.exp (L z) * ∫ x, φ x ∂(D.measure.map alphaQ) := by
    rw [hq φ hφc hφ z, hL z]
  obtain ⟨κ, hκ⟩ := RealIwasawa.withDensity_eq_smul_volume _ L hL'
  refine ⟨κ, -L, fun B hB => ?_⟩
  rw [← lintegral_map hB hα, RealIwasawa.lintegral_eq_of_withDensity_eq _ L κ hκ hB]
  simp only [_root_.neg_apply]

end Weil
end ComplexLocalIwasawa

open ArchimedeanLocal ComplexLocalIwasawa

/-- The logarithmic toral marginal of each compatible complex quotient measure is a finite
multiple of Lebesgue measure with exponential linear density. -/
def ComplexIwasawaToralMeasureStatement : Prop :=
  ∀ (t : ℕ) (D : ComplexQuotientMeasureData t),
    ∃ (κ : ℝ≥0) (L : (Fin (t + 1) → ℝ) →L[ℝ] ℝ),
      ∀ B : (Fin (t + 1) → ℝ) → ℝ≥0∞, Measurable B →
        ∫⁻ q, B (alphaQ q) ∂D.measure =
          (κ : ℝ≥0∞) * ∫⁻ x, ENNReal.ofReal (Real.exp (L x)) * B x

theorem complexIwasawaToralMeasure : ComplexIwasawaToralMeasureStatement := by
  intro t D
  exact exists_lintegral_alphaQ D

end Langlands.Global.RankinSelbergGlobal
