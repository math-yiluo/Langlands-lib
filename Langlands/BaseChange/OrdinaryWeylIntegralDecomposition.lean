import Langlands.BaseChange.OrdinaryWeylMeasureDecomposition
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Integral.Prod

/-! # Integration against the ordinary Weyl product measures -/

namespace Langlands.Analysis

open MeasureTheory
open scoped ENNReal NNReal

variable {Q A E : Type*} [MeasurableSpace Q] [MeasurableSpace A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fubini for a product measure weighted by a positive measurable density on the
second factor. The weighted inner integral is integrable and its integral of the
norm is bounded by the original product integral of the norm. -/
theorem integral_prod_withDensity_snd {ν : Measure Q} {τ : Measure A}
    [SFinite ν] [SFinite τ] {w : A → ℝ≥0} (hw : Measurable w)
    (hpos : ∀ᵐ t ∂τ, 0 < w t) {g : Q × A → E}
    (hg : Integrable g ((ν.prod τ).withDensity (fun z => (w z.2 : ℝ≥0∞)))) :
    let H (t : A) := (w t : ℝ) • ∫ q, g (q, t) ∂ν
    (∀ᵐ t ∂τ, Integrable (fun q => g (q, t)) ν) ∧ Integrable H τ ∧
      (∫ z, g z ∂(ν.prod τ).withDensity (fun z => (w z.2 : ℝ≥0∞))) = ∫ t, H t ∂τ ∧
      (∫ t, ‖H t‖ ∂τ) ≤
        ∫ z, ‖g z‖ ∂(ν.prod τ).withDensity (fun z => (w z.2 : ℝ≥0∞)) := by
  dsimp only
  have hwprod : Measurable (fun z : Q × A => w z.2) := hw.comp measurable_snd
  have hh := (integrable_withDensity_iff_integrable_coe_smul hwprod).mp hg
  have houter : Integrable (fun t => (w t : ℝ) • ∫ q, g (q, t) ∂ν) τ := by
    simpa only [integral_smul] using hh.integral_prod_right
  refine ⟨?_, houter, ?_, ?_⟩
  · filter_upwards [hh.prod_left_ae, hpos] with t ht htpos
    have hwne : (w t : ℝ) ≠ 0 := by exact_mod_cast htpos.ne'
    have hinv := ht.smul (w t : ℝ)⁻¹
    change Integrable (fun q => (w t : ℝ)⁻¹ • ((w t : ℝ) • g (q, t))) ν at hinv
    simpa only [smul_smul, inv_mul_cancel₀ hwne, one_smul] using hinv
  · rw [integral_withDensity_eq_integral_smul hwprod]
    simpa only [NNReal.smul_def, integral_smul] using integral_prod_symm _ hh
  · calc
      (∫ t, ‖(w t : ℝ) • ∫ q, g (q, t) ∂ν‖ ∂τ) ≤
          ∫ t, ∫ q, ‖(w t : ℝ) • g (q, t)‖ ∂ν ∂τ := by
        refine integral_mono houter.norm hh.integral_norm_prod_right fun t => ?_
        rw [← integral_smul]
        exact norm_integral_le_integral_norm _
      _ = ∫ z, ‖(w z.2 : ℝ) • g z‖ ∂ν.prod τ := (integral_prod_symm _ hh.norm).symm
      _ = ∫ z, ‖g z‖ ∂(ν.prod τ).withDensity (fun z => (w z.2 : ℝ≥0∞)) := by
        rw [integral_withDensity_eq_integral_smul hwprod]
        simp only [NNReal.smul_def, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg (NNReal.coe_nonneg _), smul_eq_mul]

end Langlands.Analysis

namespace Langlands.BaseChange

open Langlands.JacquetLanglands Langlands.QuotientIntegration
open MeasureTheory Set Topology
open scoped ENNReal NNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u

namespace WeylTorus

variable {F : Type u} [Field F] [TopologicalSpace F]
  {n : ℕ} [MeasurableSpace (GeneralLinear n F)]

/-- The weighted measure on the ordinary Weyl map source. The density depends
only on the torus coordinate. -/
noncomputable def weightedOrdinaryOrbitMeasure (T : WeylTorus F n)
    (ν : Measure (LeftQuotient T.val)) (τ : Measure T.regularPoints)
    (w : T.regularPoints → ℝ≥0) : Measure (LeftQuotient T.val × T.regularPoints) :=
  (ν.prod τ).withDensity fun z => (w z.2 : ℝ≥0∞)

/-- The weighted inner integral on regular torus points, with the reciprocal
rational Weyl order. -/
noncomputable def ordinaryOrbitIntegrand (T : WeylTorus F n)
    (ν : Measure (LeftQuotient T.val)) (w : T.regularPoints → ℝ≥0)
    (f : GeneralLinear n F → ℂ) (t : T.regularPoints) : ℂ :=
  ((Nat.card T.RationalWeylGroup : ℝ≥0∞)⁻¹).toReal •
    ((w t : ℝ) • ∫ q, f (T.ordinaryOrbitMap (q, t)) ∂ν)

end WeylTorus

/-- Integrating the ordinary Weyl measure sum gives the iterated formula
on the regular locus and absolute convergence of the torus integrals. -/
def OrdinaryWeylIntegralDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (n : ℕ)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    (μ : Measure (GeneralLinear n F)) (S : Set (WeylTorus F n)),
    WeylTorus.IsRepresentativeSet S →
    ∀ (ν : ∀ T : S, Measure (LeftQuotient T.val.val))
      (τ : ∀ T : S, Measure T.val.regularPoints)
      (w : ∀ T : S, T.val.regularPoints → ℝ≥0),
      (∀ T : S, SFinite (ν T)) → (∀ T : S, SFinite (τ T)) →
      (∀ T : S, Measurable (w T)) → (∀ T : S, ∀ᵐ t ∂τ T, 0 < w T t) →
      (∀ T : S, T.val.HasOrdinaryLocalPushforwards μ
        (T.val.weightedOrdinaryOrbitMeasure (ν T) (τ T) (w T))) →
      ∀ f : GeneralLinear n F → ℂ, IntegrableOn f {g | IsRegularSemisimple g} μ →
        (∀ T : S, ∀ᵐ t ∂τ T,
          Integrable (fun q => f (T.val.ordinaryOrbitMap (q, t))) (ν T)) ∧
        (∀ T : S, Integrable (T.val.ordinaryOrbitIntegrand (ν T) (w T) f) (τ T)) ∧
        Summable (fun T : S => ∫ t, ‖T.val.ordinaryOrbitIntegrand (ν T) (w T) f t‖ ∂τ T) ∧
        (∫ g in {g | IsRegularSemisimple g}, f g ∂μ) =
          ∑' T : S, ∫ t, T.val.ordinaryOrbitIntegrand (ν T) (w T) f t ∂τ T

theorem ordinaryWeylIntegralDecomposition : OrdinaryWeylIntegralDecompositionStatement.{u} := by
  intro F _ _ _ _ n _ _ μ S hS ν τ w hν hτ hw hpos hlocal f hf
  let ρ (T : S) := T.val.weightedOrdinaryOrbitMeasure (ν T) (τ T) (w T)
  let c (T : S) := (Nat.card T.val.RationalWeylGroup : ℝ≥0∞)⁻¹
  let p (T : S) := T.val.ordinaryOrbitMap
  let μpart (T : S) := c T • (ρ T).map (p T)
  obtain ⟨_, hsum⟩ := ordinaryWeylMeasureDecomposition F n μ S hS ρ hlocal
  change μ.restrict {g | IsRegularSemisimple g} = Measure.sum μpart at hsum
  have hfsum : Integrable f (Measure.sum μpart) := hsum ▸ hf
  have hfmap (T : S) : Integrable f ((ρ T).map (p T)) := by
    rw [T.val.map_ordinaryOrbitMap (hlocal T)]
    have hfr : Integrable f (μ.restrict (range (p T))) :=
      hf.mono_set fun _ hg => by
        obtain ⟨x, rfl⟩ := hg
        exact T.val.isRegularSemisimple_ordinaryOrbitMap x
    exact hfr.smul_measure (by simp)
  have hp (T : S) : Measurable (p T) := by
    let : SecondCountableTopology (GeneralLinear n F) :=
      LocalFieldTopology.generalLinear_secondCountableTopology F n
    let : SecondCountableTopology (LeftQuotient T.val.val) :=
      (leftQuotient_isOpenQuotientMap T.val.val).secondCountableTopology
    let : SecondCountableTopology T.val.val := IsInducing.subtypeVal.secondCountableTopology
    let : SecondCountableTopology T.val.regularPoints :=
      IsInducing.subtypeVal.secondCountableTopology
    exact T.val.continuous_ordinaryOrbitMap.measurable
  let H (T : S) (t : T.val.regularPoints) :=
    (w T t : ℝ) • ∫ q, f (p T (q, t)) ∂ν T
  have hFubini (T : S) :
      (∀ᵐ t ∂τ T, Integrable (fun q => f (p T (q, t))) (ν T)) ∧
        Integrable (H T) (τ T) ∧
        (∫ z, f (p T z) ∂ρ T) = ∫ t, H T t ∂τ T ∧
        (∫ t, ‖H T t‖ ∂τ T) ≤ ∫ z, ‖f (p T z)‖ ∂ρ T := by
    have := hν T
    have := hτ T
    exact Analysis.integral_prod_withDensity_snd (hw T) (hpos T)
      ((hfmap T).comp_measurable (hp T))
  let J (T : S) := T.val.ordinaryOrbitIntegrand (ν T) (w T) f
  have hJInt (T : S) : Integrable (J T) (τ T) := (hFubini T).2.1.smul (c T).toReal
  have hJBound (T : S) : (∫ t, ‖J T t‖ ∂τ T) ≤ ∫ g, ‖f g‖ ∂μpart T := by
    change (∫ t, ‖(c T).toReal • H T t‖ ∂τ T) ≤
      ∫ g, ‖f g‖ ∂c T • (ρ T).map (p T)
    have heq (t : T.val.regularPoints) :
        ‖(c T).toReal • H T t‖ = (c T).toReal • ‖H T t‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg, smul_eq_mul]
    simp_rw [heq, integral_smul, integral_smul_measure,
      integral_map (hp T).aemeasurable (hfmap T).norm.aestronglyMeasurable]
    exact mul_le_mul_of_nonneg_left (hFubini T).2.2.2 ENNReal.toReal_nonneg
  refine ⟨fun T => (hFubini T).1, hJInt, ?_, ?_⟩
  · exact Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      hJBound hfsum.summable_integral
  · rw [hsum, integral_sum_measure hfsum]
    apply tsum_congr
    intro T
    change (∫ g, f g ∂c T • (ρ T).map (p T)) =
      ∫ t, (c T).toReal • H T t ∂τ T
    rw [integral_smul_measure, integral_map (hp T).aemeasurable (hfmap T).aestronglyMeasurable,
      (hFubini T).2.2.1, integral_smul]

end Langlands.BaseChange
