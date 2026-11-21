import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.WithDensity

/-! # Translation operators on classes with invariant representatives

On `L²((μ|_D).withDensity W)`, left translation by `b` is not defined on arbitrary classes, but it is
defined and bounded on classes that have representatives in a class `P` of functions on which
translation satisfies a weighted `L²` bound. This module builds the composite "translate by `b`
after `T`" for every operator `T` whose values have such representatives. -/

noncomputable section

open MeasureTheory Set Function
open scoped ENNReal

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Analysis.InvariantTranslation

variable {H : Type*} [Group H] [MeasurableSpace H] [MeasurableMul H]
  (μ : Measure H) (D : Set H) (W : H → ℝ≥0∞) (b : H)

/-- The weighted measure `(μ|_D).withDensity W`. -/
abbrev weighted : Measure H := (μ.restrict D).withDensity W

variable {μ D W}

theorem lintegral_weighted (hW : Measurable W) {φ : H → ℝ≥0∞} (hφ : Measurable φ) :
    ∫⁻ g, φ g ∂(weighted μ D W) = ∫⁻ g in D, φ g * W g ∂μ := by
  rw [lintegral_withDensity_eq_lintegral_mul _ hW hφ]
  exact lintegral_congr fun g => mul_comm _ _

variable (P : (H → ℂ) → Prop) (K : ℝ≥0∞)

/-- If `P` is closed under subtraction and translation by `b` is bounded on `P`, translation by
`b` respects almost-everywhere equality of measurable functions in `P`. -/
theorem translate_ae_congr (hW : Measurable W) (hsub : ∀ f g, P f → P g → P (f - g))
    (hbound : ∀ f, Measurable f → P f →
      ∫⁻ g in D, ‖f (b * g)‖ₑ ^ 2 * W g ∂μ ≤ K * ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ)
    {f₁ f₂ : H → ℂ} (hf₁ : Measurable f₁) (hf₂ : Measurable f₂) (hP₁ : P f₁) (hP₂ : P f₂)
    (h : f₁ =ᵐ[weighted μ D W] f₂) :
    (fun g => f₁ (b * g)) =ᵐ[weighted μ D W] fun g => f₂ (b * g) := by
  have hd : Measurable (f₁ - f₂) := hf₁.sub hf₂
  have h0 : ∫⁻ g in D, ‖(f₁ - f₂) g‖ₑ ^ 2 * W g ∂μ = 0 := by
    rw [← lintegral_weighted hW ((hd.enorm).pow_const 2)]
    refine lintegral_eq_zero_iff ((hd.enorm).pow_const 2) |>.mpr ?_
    filter_upwards [h] with g hg
    simp [hg]
  have hb := hbound _ hd (hsub _ _ hP₁ hP₂)
  rw [h0, mul_zero, nonpos_iff_eq_zero] at hb
  have hφ : Measurable fun g => ‖(f₁ - f₂) (b * g)‖ₑ ^ 2 :=
    ((hd.comp (measurable_const_mul b)).enorm).pow_const 2
  have hb' : ∫⁻ g, ‖(f₁ - f₂) (b * g)‖ₑ ^ 2 ∂(weighted μ D W) = 0 :=
    (lintegral_weighted hW hφ).trans hb
  have hz := (lintegral_eq_zero_iff hφ).mp hb'
  filter_upwards [hz] with g hg
  have : ‖(f₁ - f₂) (b * g)‖ₑ = 0 := by
    simpa using hg
  rw [enorm_eq_zero, Pi.sub_apply, sub_eq_zero] at this
  exact this

theorem eLpNorm_translate_le (hW : Measurable W)
    (hbound : ∀ f, Measurable f → P f →
      ∫⁻ g in D, ‖f (b * g)‖ₑ ^ 2 * W g ∂μ ≤ K * ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ)
    {f : H → ℂ} (hf : Measurable f) (hP : P f) :
    eLpNorm (fun g => f (b * g)) 2 (weighted μ D W) ≤
      K ^ (1 / 2 : ℝ) * eLpNorm f 2 (weighted μ D W) := by
  have hfb : Measurable fun g => f (b * g) := hf.comp (measurable_const_mul b)
  have hsq : ∀ {φ : H → ℂ}, Measurable φ →
      ∫⁻ g, ‖φ g‖ₑ ^ (2 : ℝ≥0∞).toReal ∂(weighted μ D W) = ∫⁻ g in D, ‖φ g‖ₑ ^ 2 * W g ∂μ := by
    intro φ hφ
    rw [show (2 : ℝ≥0∞).toReal = (2 : ℝ) by norm_num]
    simp_rw [ENNReal.rpow_two]
    exact lintegral_weighted hW (hφ.enorm.pow_const 2)
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hfb.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top
      hf.aestronglyMeasurable, hsq hfb, hsq hf,
    show (1 : ℝ) / (2 : ℝ≥0∞).toReal = 1 / 2 by norm_num,
    ← ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  exact ENNReal.rpow_le_rpow (hbound f hf hP) (by norm_num)

section Operator

variable (hW : Measurable W) (hsub : ∀ f g, P f → P g → P (f - g))
  (hadd : ∀ f g, P f → P g → P (f + g)) (hsmul : ∀ (c : ℂ) f, P f → P (c • f))
  (hKtop : K ≠ ∞)
  (hbound : ∀ f, Measurable f → P f →
    ∫⁻ g in D, ‖f (b * g)‖ₑ ^ 2 * W g ∂μ ≤ K * ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ)
  (T : Lp ℂ 2 (weighted μ D W) →L[ℂ] Lp ℂ 2 (weighted μ D W))
  (hT : ∀ Fn, ∃ h : H → ℂ, Measurable h ∧ P h ∧ h =ᵐ[weighted μ D W] T Fn)

/-- A measurable representative of `T Fn` with property `P`. -/
def invRep (Fn : Lp ℂ 2 (weighted μ D W)) : H → ℂ := (hT Fn).choose

theorem invRep_spec (Fn : Lp ℂ 2 (weighted μ D W)) :
    Measurable (invRep P T hT Fn) ∧ P (invRep P T hT Fn) ∧
      invRep P T hT Fn =ᵐ[weighted μ D W] T Fn :=
  (hT Fn).choose_spec

include hW hKtop hbound in
theorem memLp_translate (Fn : Lp ℂ 2 (weighted μ D W)) :
    MemLp (fun g => invRep P T hT Fn (b * g)) 2 (weighted μ D W) := by
  obtain ⟨hm, hP, hae⟩ := invRep_spec P T hT Fn
  refine (eLpNorm_translate_le b P K hW hbound hm hP).trans_lt (ENNReal.mul_lt_top ?_ ?_)
  · exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKtop
  · rw [eLpNorm_congr_ae hae]
    exact Lp.eLpNorm_lt_top _

include hW hKtop hbound in
/-- Translation by `b` of `T Fn`, computed on an invariant representative. -/
def translateLp (Fn : Lp ℂ 2 (weighted μ D W)) : Lp ℂ 2 (weighted μ D W) :=
  (memLp_translate b P K hW hKtop hbound T hT Fn).toLp _

include hsub in
theorem translateLp_ae_of (Fn : Lp ℂ 2 (weighted μ D W)) {h : H → ℂ} (hm : Measurable h)
    (hP : P h) (hh : h =ᵐ[weighted μ D W] T Fn) :
    translateLp b P K hW hKtop hbound T hT Fn =ᵐ[weighted μ D W] fun g => h (b * g) := by
  obtain ⟨hm', hP', hae'⟩ := invRep_spec P T hT Fn
  refine (MemLp.coeFn_toLp _).trans ?_
  exact translate_ae_congr b P K hW hsub hbound hm' hm hP' hP (hae'.trans hh.symm)

include hsub hadd hsmul in
/-- **Translation after `T`** as a continuous linear operator, of norm at most
`K^{1/2} ‖T‖`. -/
def translateCLM : Lp ℂ 2 (weighted μ D W) →L[ℂ] Lp ℂ 2 (weighted μ D W) :=
  LinearMap.mkContinuous
    { toFun := translateLp b P K hW hKtop hbound T hT
      map_add' := fun F G => by
        obtain ⟨hmF, hPF, haeF⟩ := invRep_spec P T hT F
        obtain ⟨hmG, hPG, haeG⟩ := invRep_spec P T hT G
        apply Lp.ext
        have hsum : invRep P T hT F + invRep P T hT G =ᵐ[weighted μ D W] T (F + G) := by
          filter_upwards [haeF, haeG, Lp.coeFn_add (T F) (T G)] with g h1 h2 h3
          rw [map_add, Pi.add_apply, h1, h2, h3, Pi.add_apply]
        filter_upwards [translateLp_ae_of b P K hW hsub hKtop hbound T hT (F + G) (hmF.add hmG)
            (hadd _ _ hPF hPG) hsum,
          translateLp_ae_of b P K hW hsub hKtop hbound T hT F hmF hPF haeF,
          translateLp_ae_of b P K hW hsub hKtop hbound T hT G hmG hPG haeG,
          Lp.coeFn_add (translateLp b P K hW hKtop hbound T hT F)
            (translateLp b P K hW hKtop hbound T hT G)] with g h1 h2 h3 h4
        rw [h1, h4]
        simp only [Pi.add_apply]
        rw [h2, h3]
      map_smul' := fun c F => by
        obtain ⟨hmF, hPF, haeF⟩ := invRep_spec P T hT F
        apply Lp.ext
        have hsm : c • invRep P T hT F =ᵐ[weighted μ D W] T (c • F) := by
          filter_upwards [haeF, Lp.coeFn_smul c (T F)] with g h1 h2
          rw [map_smul, Pi.smul_apply, h1, h2, Pi.smul_apply]
        filter_upwards [translateLp_ae_of b P K hW hsub hKtop hbound T hT (c • F)
            (hmF.const_smul c) (hsmul c _ hPF) hsm,
          translateLp_ae_of b P K hW hsub hKtop hbound T hT F hmF hPF haeF,
          Lp.coeFn_smul c (translateLp b P K hW hKtop hbound T hT F)] with g h1 h2 h3
        rw [h1, RingHom.id_apply, h3]
        simp only [Pi.smul_apply]
        rw [h2] }
    ((K ^ (1 / 2 : ℝ)).toReal * ‖T‖) (fun F => by
      obtain ⟨hmF, hPF, haeF⟩ := invRep_spec P T hT F
      change ‖translateLp b P K hW hKtop hbound T hT F‖ ≤ _
      rw [Lp.norm_def, mul_assoc]
      have hK' : K ^ (1 / 2 : ℝ) ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKtop).ne
      calc (eLpNorm (translateLp b P K hW hKtop hbound T hT F) 2 (weighted μ D W)).toReal
          = (eLpNorm (fun g => invRep P T hT F (b * g)) 2 (weighted μ D W)).toReal := by
            unfold translateLp
            rw [eLpNorm_congr_ae (MemLp.coeFn_toLp _)]
        _ ≤ (K ^ (1 / 2 : ℝ) * eLpNorm (invRep P T hT F) 2 (weighted μ D W)).toReal :=
            ENNReal.toReal_mono (ENNReal.mul_ne_top hK'
              (by rw [eLpNorm_congr_ae haeF]; exact Lp.eLpNorm_ne_top _))
              (eLpNorm_translate_le b P K hW hbound hmF hPF)
        _ = (K ^ (1 / 2 : ℝ)).toReal * ‖T F‖ := by
            rw [ENNReal.toReal_mul, eLpNorm_congr_ae haeF, Lp.norm_def]
        _ ≤ (K ^ (1 / 2 : ℝ)).toReal * (‖T‖ * ‖F‖) :=
            mul_le_mul_of_nonneg_left (T.le_opNorm F) ENNReal.toReal_nonneg)

theorem translateCLM_ae (Fn : Lp ℂ 2 (weighted μ D W)) {h : H → ℂ} (hm : Measurable h)
    (hP : P h) (hh : h =ᵐ[weighted μ D W] T Fn) :
    translateCLM b P K hW hsub hadd hsmul hKtop hbound T hT Fn =ᵐ[weighted μ D W]
      fun g => h (b * g) :=
  translateLp_ae_of b P K hW hsub hKtop hbound T hT Fn hm hP hh

theorem norm_translateCLM_le :
    ‖translateCLM b P K hW hsub hadd hsmul hKtop hbound T hT‖ ≤
      (K ^ (1 / 2 : ℝ)).toReal * ‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (mul_nonneg ENNReal.toReal_nonneg (norm_nonneg _)) _

end Operator

universe u

/-- **Statement form.** Let `μ` be a measure on a measurable group `H`, `D ⊆ H`, `W ≥ 0` a measurable
weight, `b ∈ H`, `P` a class of functions closed under addition, subtraction and scalar
multiplication, and `K < ∞` such that `∫_D ‖f(b g)‖² W ≤ K ∫_D ‖f‖² W` for measurable `f` in `P`.
For every continuous linear `T` on `L²((μ|_D).withDensity W)` whose values have measurable
representatives in `P`, there is a continuous linear operator of norm at most `K^{1/2} ‖T‖` that
sends `Fn` to the class of `g ↦ h(b g)` for every measurable representative `h ∈ P` of `T Fn`. -/
def InvariantTranslationStatement : Prop :=
  ∀ {H : Type u} [Group H] [MeasurableSpace H] [MeasurableMul H] (μ : Measure H) (D : Set H)
    (W : H → ℝ≥0∞), Measurable W → ∀ (b : H) (P : (H → ℂ) → Prop) (K : ℝ≥0∞),
    (∀ f g, P f → P g → P (f - g)) → (∀ f g, P f → P g → P (f + g)) →
    (∀ (c : ℂ) f, P f → P (c • f)) → K ≠ ∞ →
    (∀ f, Measurable f → P f →
      ∫⁻ g in D, ‖f (b * g)‖ₑ ^ 2 * W g ∂μ ≤ K * ∫⁻ g in D, ‖f g‖ₑ ^ 2 * W g ∂μ) →
    ∀ (T : Lp ℂ 2 (weighted μ D W) →L[ℂ] Lp ℂ 2 (weighted μ D W)),
    (∀ Fn, ∃ h : H → ℂ, Measurable h ∧ P h ∧ h =ᵐ[weighted μ D W] T Fn) →
    ∃ L : Lp ℂ 2 (weighted μ D W) →L[ℂ] Lp ℂ 2 (weighted μ D W),
      ‖L‖ ≤ (K ^ (1 / 2 : ℝ)).toReal * ‖T‖ ∧
      ∀ (Fn : Lp ℂ 2 (weighted μ D W)) {h : H → ℂ}, Measurable h → P h →
        h =ᵐ[weighted μ D W] T Fn → L Fn =ᵐ[weighted μ D W] fun g => h (b * g)

/-- Proof of `InvariantTranslationStatement`. -/
theorem invariantTranslation : InvariantTranslationStatement.{u} := by
  intro H _ _ _ μ D W hW b P K hsub hadd hsmul hKtop hbound T hT
  exact ⟨translateCLM b P K hW hsub hadd hsmul hKtop hbound T hT,
    norm_translateCLM_le b P K hW hsub hadd hsmul hKtop hbound T hT,
    fun Fn _ hm hP hh => translateCLM_ae b P K hW hsub hadd hsmul hKtop hbound T hT Fn hm hP hh⟩

end Langlands.Analysis.InvariantTranslation
