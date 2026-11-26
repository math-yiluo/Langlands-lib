import Langlands.Automorphic.GroupSchemeQuotientL2CompactPart
import Langlands.Automorphic.CuspidalAdmissible.Finiteness
import Mathlib.Topology.UrysohnsLemma

/-! # Small right oscillation of compact convolution -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Topology Set Filter
open scoped CategoryTheory.MonObj CompactlySupported Pointwise Topology
open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme

namespace Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F G)).IsMulRightInvariant]

local notation "A" => AdelicGroupPoints F G
local notation "Q" => PositiveRationalQuotient F G T i
local notation "Γ" => positiveRationalSubgroup F G T i
local notation "mQ" => positiveRationalQuotientHaarMeasure F G T i
local notation "mG" => (Measure.haar : Measure A)
local notation "E" => Lp ℂ 2 mQ
local notation "R" => haarQuotientL2IntegratedAction F G T i hi I e hc mG

set_option maxHeartbeats 400000 in
private theorem exists_translation_envelope {H : Type*} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] (f : C_c(H, ℂ)) :
    ∃ b : C_c(H, ℝ), (∀ g, 0 ≤ b g) ∧
      ∀ ε > 0, ∃ U ∈ 𝓝 (1 : H), ∀ a ∈ U, ∀ g, ‖f g - f (a⁻¹ * g)‖ ≤ ε * b g := by
  obtain ⟨V, hVc, hV⟩ := exists_compact_mem_nhds (1 : H)
  let D := (V * tsupport f) ∪ tsupport f
  have hD : IsCompact D := (hVc.mul f.hasCompactSupport).union f.hasCompactSupport
  obtain ⟨b, hb₁, _, hbc, hb01⟩ := exists_continuous_one_zero_of_isCompact hD
    isClosed_empty (Set.disjoint_empty _)
  let b' : C_c(H, ℝ) := ⟨b, hbc⟩
  refine ⟨b', fun g => (hb01 g).1, ?_⟩
  intro ε hε
  obtain ⟨U, hU, hU₁, ht⟩ := OperatorRealization.exists_nhds_one_norm_sub_lt
    (f.continuous.comp continuous_inv) (f.hasCompactSupport.comp_homeomorph (Homeomorph.inv H)) hε
  refine ⟨U ∩ V, Filter.inter_mem (hU.mem_nhds hU₁) hV, ?_⟩
  intro a ha g
  by_cases hg : g ∈ D
  · change ‖f g - f (a⁻¹ * g)‖ ≤ ε * b g
    rw [show b g = 1 from hb₁ hg, mul_one, norm_sub_rev]
    have h := ht a ha.1 g⁻¹
    change ‖f (g⁻¹ * a)⁻¹ - f (g⁻¹)⁻¹‖ < ε at h
    simpa only [mul_inv_rev, inv_inv] using h.le
  · have hg₁ : f g = 0 := image_eq_zero_of_notMem_tsupport (fun h => hg (Or.inr h))
    have hg₂ : f (a⁻¹ * g) = 0 := image_eq_zero_of_notMem_tsupport (fun h =>
      hg (Or.inl ⟨a, ha.2, a⁻¹ * g, h, by simp⟩))
    rw [hg₁, hg₂, sub_zero, norm_zero]
    exact mul_nonneg hε.le (hb01 g).1

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2100000 in
/-- For each compact continuous weight and each positive tolerance, the right oscillations of
its convolution are pointwise dominated, almost everywhere and uniformly over a common identity
neighborhood, by the tolerance times an `L²` class of bounded norm. -/
theorem exists_positiveQuotientL2ConvolutionOscillation (f : C_c(A, ℂ)) (hf : Integrable f mG) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε > 0, ∃ U ∈ 𝓝 (1 : A), ∀ φ : E,
      ∃ (ψ : C(Q, ℂ)) (b : E), (R f hf φ : Q → ℂ) =ᵐ[mQ] ψ ∧ ‖b‖ ≤ C * ‖φ‖ ∧
        ∀ᵐ q ∂mQ, ∀ a ∈ U, ‖ψ q - ψ (LeftCosetSpace.rightTranslate Γ a q)‖ ≤ ε * ‖b q‖ := by
  let : BorelSpace Q := positiveRationalQuotient_borelSpace F G T i hi I e hc
  let : IsLocallyFiniteMeasure mQ := positiveRationalQuotientHaarMeasure_isLocallyFiniteMeasure F G T i hi I e hc
  obtain ⟨k, hkc, hpoint, hrep⟩ := exists_positiveQuotientL2ConvolutionRows F G T i hi I e hc f hf
  obtain ⟨b₀, hb₀, hnear⟩ := exists_translation_envelope f
  let b : C_c(A, ℂ) := ⟨⟨fun g => b₀ g, Complex.continuous_ofReal.comp b₀.continuous⟩,
    b₀.hasCompactSupport.comp_left Complex.ofReal_zero⟩
  have hb : Integrable b mG := b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  obtain ⟨kb, _, hpb, hrb⟩ := exists_positiveQuotientL2ConvolutionRows F G T i hi I e hc b hb
  let C := ∫ g, ‖b g‖ ∂mG
  have hC : 0 ≤ C := integral_nonneg fun _ => norm_nonneg _
  refine ⟨C, hC, fun ε hε => ?_⟩
  obtain ⟨U, hU, hctrl⟩ := hnear ε hε
  refine ⟨U, hU, fun φ => ?_⟩
  let ψ : C(Q, ℂ) := ⟨fun q => inner ℂ (k q) φ, hkc.inner continuous_const⟩
  let hm : MemLp (fun q : Q => (‖φ q‖ : ℂ)) 2 mQ := (Lp.memLp φ).norm.ofReal
  let absφ := hm.toLp (fun q => (‖φ q‖ : ℂ))
  have hnorm : ‖absφ‖ ≤ ‖φ‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hm.coeFn_toLp] with q hq
    change ‖absφ q‖ ≤ ‖φ q‖
    rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  let B := R b hb absφ
  have hB : ‖B‖ ≤ C * ‖φ‖ := by
    have hR := norm_haarQuotientL2IntegratedAction_le F G T i hi I e hc mG b hb
    exact ((R b hb).le_opNorm absφ).trans
      ((mul_le_mul_of_nonneg_right hR (norm_nonneg _)).trans (mul_le_mul_of_nonneg_left hnorm hC))
  refine ⟨ψ, B, hrep φ, hB, ?_⟩
  let act (q : Q) (g : A) := LeftCosetSpace.rightTranslate Γ g q
  let hM := (continuous_positiveQuotient_rightTranslate F G T i).measurable
  let hinv := haarQuotientMeasureRightInvariant F G T i hi I e hc
  have hpaired : ∀ᵐ q ∂mQ, ∀ᵐ g ∂mG, absφ (act q g) = (‖φ (act q g)‖ : ℂ) := by
    have h1 := (Lp.stronglyMeasurable absφ).comp_measurable hM
    have h2 := (Complex.continuous_ofReal.comp continuous_norm).comp_stronglyMeasurable
      ((Lp.stronglyMeasurable φ).comp_measurable hM)
    exact (Measure.ae_ae_comm (h1.measurableSet_eq_fun h2)).mpr (Eventually.of_forall fun g =>
      (hinv g).quasiMeasurePreserving.ae_eq_comp hm.coeFn_toLp)
  filter_upwards [hrb absφ, hpaired] with q hq hqa
  obtain ⟨x, rfl⟩ := LeftCosetSpace.mk_surjective Γ q
  let P (g : A) := φ (LeftCosetSpace.mk Γ (x * g))
  have hBval : ‖B (LeftCosetSpace.mk Γ x)‖ = ∫ g, ‖b g * P g‖ ∂mG := by
    change B (LeftCosetSpace.mk Γ x) = inner ℂ (kb (LeftCosetSpace.mk Γ x)) absφ at hq
    rw [hq, (hpb x absφ).2]
    have heq : ∀ᵐ g ∂mG, b g * absφ (LeftCosetSpace.mk Γ (x * g)) = (‖b g * P g‖ : ℂ) := by
      filter_upwards [hqa] with g hg
      change absφ (LeftCosetSpace.mk Γ (x * g)) = (‖P g‖ : ℂ) at hg
      rw [hg, norm_mul]
      simp only [b, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
        Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb₀ g), Complex.ofReal_mul]
    rw [integral_congr_ae heq, integral_complex_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
  intro a ha
  change ‖inner ℂ (k (LeftCosetSpace.mk Γ x)) φ - inner ℂ (k (LeftCosetSpace.mk Γ (x * a))) φ‖ ≤ _
  rw [(hpoint x φ).2, (hpoint (x * a) φ).2, hBval]
  let L (g : A) := f (a⁻¹ * g) * P g
  have hL : Integrable L mG := by
    simpa only [L, P, mul_assoc, mul_inv_cancel_left] using ((hpoint (x * a) φ).1.comp_mul_left a⁻¹)
  have htrans : (∫ g, f g * φ (LeftCosetSpace.mk Γ (x * a * g)) ∂mG) = ∫ g, L g ∂mG := by
    rw [← integral_mul_left_eq_self («μ» := mG) L a]
    apply integral_congr_ae (Eventually.of_forall fun g => ?_)
    simp only [L, P, inv_mul_cancel_left, mul_assoc]
  rw [htrans, ← integral_sub (hpoint x φ).1 hL, ← integral_const_mul]
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono ((hpoint x φ).1.sub hL).norm ((hpb x φ).1.norm.const_mul ε)
  intro g
  change ‖f g * P g - f (a⁻¹ * g) * P g‖ ≤ ε * ‖b g * P g‖
  rw [← sub_mul, norm_mul, norm_mul, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa only [b, CompactlySupportedContinuousMap.coe_mk, ContinuousMap.coe_mk,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb₀ g)] using hctrl a ha g

end Langlands.Automorphic.GroupSchemeFunctions
