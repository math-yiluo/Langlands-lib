import Langlands.BaseChange.OrdinaryWeylIntegralDecomposition
import Langlands.BaseChange.TwistedWeylMeasureDecomposition

/-! # Integration against the twisted Weyl product measures -/

namespace Langlands.BaseChange

open Langlands.QuotientIntegration
open MeasureTheory Set
open scoped ENNReal NNReal

attribute [local instance high] leftQuotientMeasurableSpace
attribute [local instance] leftQuotient_borelSpace

universe u v

namespace WeylTorus

variable {F : Type u} [Field F] [TopologicalSpace F]
  {E : Type v} [CommRing E] [Algebra F E] [TopologicalSpace E]
  {n : ℕ} [MeasurableSpace (GeneralLinear n F)]

/-- The source measure of twisted Weyl conjugation with a density in the
regular norm-image coordinate. -/
noncomputable def weightedTwistedOrbitMeasure (T : WeylTorus F n)
    (σ : E ≃ₐ[F] E) (l : ℕ)
    (ν : Measure (LeftQuotient (T.val.map (baseChange F E n))))
    (τ : Measure (T.regularNormPoints σ l)) (w : T.regularNormPoints σ l → ℝ≥0) :
    Measure (LeftQuotient (T.val.map (baseChange F E n)) × T.regularNormPoints σ l) :=
  (ν.prod τ).withDensity fun z => (w z.2 : ℝ≥0∞)

variable [ValuativeRel F] [IsNonarchimedeanLocalField F]
  [IsTopologicalRing E] [IsModuleTopology F E] {σ : E ≃ₐ[F] E} {l : ℕ}

/-- The weighted twisted inner integral on regular norm-image points, with
the reciprocal rational Weyl order. -/
noncomputable def twistedOrbitIntegrand (T : WeylTorus F n) (hσ : IsCyclicAlgebra σ l)
    (lift : T.regularNormPoints σ l → T.points E)
    (hlift : ∀ t, cyclicNorm σ l (lift t).val = baseChange F E n t.val.val)
    (ν : Measure (LeftQuotient (T.val.map (baseChange F E n))))
    (w : T.regularNormPoints σ l → ℝ≥0) (f : GeneralLinear n E → ℂ)
    (t : T.regularNormPoints σ l) : ℂ :=
  ((Nat.card T.RationalWeylGroup : ℝ≥0∞)⁻¹).toReal •
    ((w t : ℝ) • ∫ q, f (T.twistedOrbitMap hσ lift hlift (q, t)) ∂ν)

end WeylTorus

/-- Integrating the twisted Weyl measure sum gives the iterated formula on
the σ-regular locus and absolute convergence of the torus integrals. -/
def TwistedWeylIntegralDecompositionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (E : Type v) [CommRing E] [Algebra F E]
    [TopologicalSpace E] [IsTopologicalRing E] [IsModuleTopology F E]
    (σ : E ≃ₐ[F] E) (l n : ℕ) (hσ : IsCyclicAlgebra σ l)
    [MeasurableSpace (GeneralLinear n F)] [BorelSpace (GeneralLinear n F)]
    [MeasurableSpace (GeneralLinear n E)] [BorelSpace (GeneralLinear n E)]
    (μ : Measure (GeneralLinear n E)) (S : Set (WeylTorus F n)), WeylTorus.IsRepresentativeSet S →
    ∀ (lift : ∀ T : S, T.val.regularNormPoints σ l → T.val.points E)
      (hlift : ∀ (T : S) (t : T.val.regularNormPoints σ l),
        cyclicNorm σ l (lift T t).val = baseChange F E n t.val.val)
      (ν : ∀ T : S, Measure (LeftQuotient (T.val.val.map (baseChange F E n))))
      (τ : ∀ T : S, Measure (T.val.regularNormPoints σ l))
      (w : ∀ T : S, T.val.regularNormPoints σ l → ℝ≥0),
      (∀ T : S, SFinite (ν T)) → (∀ T : S, SFinite (τ T)) →
      (∀ T : S, Measurable (w T)) → (∀ T : S, ∀ᵐ t ∂τ T, 0 < w T t) →
      (∀ T : S, T.val.HasTwistedLocalPushforwards hσ (lift T) (hlift T) μ
        (T.val.weightedTwistedOrbitMeasure σ l (ν T) (τ T) (w T))) →
      ∀ f : GeneralLinear n E → ℂ, IntegrableOn f {d | IsSigmaRegular σ l d} μ →
        (∀ T : S, ∀ᵐ t ∂τ T,
          Integrable (fun q => f (T.val.twistedOrbitMap hσ (lift T) (hlift T) (q, t))) (ν T)) ∧
        let I (T : S) := T.val.twistedOrbitIntegrand hσ (lift T) (hlift T) (ν T) (w T) f
        (∀ T : S, Integrable (I T) (τ T)) ∧
        Summable (fun T : S => ∫ t, ‖I T t‖ ∂τ T) ∧
        (∫ d in {d | IsSigmaRegular σ l d}, f d ∂μ) =
          ∑' T : S, ∫ t, I T t ∂τ T

theorem twistedWeylIntegralDecomposition : TwistedWeylIntegralDecompositionStatement.{u, v} := by
  intro F _ _ _ _ E _ _ _ _ _ σ l n hσ _ _ _ _ μ S hS lift hlift ν τ w hν hτ hw hpos hlocal f hf
  let ρ (T : S) := T.val.weightedTwistedOrbitMeasure σ l (ν T) (τ T) (w T)
  let c (T : S) := (Nat.card T.val.RationalWeylGroup : ℝ≥0∞)⁻¹
  let p (T : S) := T.val.twistedOrbitMap hσ (lift T) (hlift T)
  let μpart (T : S) := c T • (ρ T).map (p T)
  have hsum : μ.restrict {d | IsSigmaRegular σ l d} = Measure.sum μpart :=
    twistedWeylMeasureDecomposition F E σ l n hσ μ S hS lift hlift ρ hlocal
  have hfsum : Integrable f (Measure.sum μpart) := hsum ▸ hf
  have hfmap (T : S) : Integrable f ((ρ T).map (p T)) := by
    rw [T.val.map_twistedOrbitMap hσ (lift T) (hlift T) (hlocal T)]
    have hfr : Integrable f (μ.restrict (range (p T))) :=
      hf.mono_set fun _ hd => by
        obtain ⟨x, rfl⟩ := hd
        exact T.val.isSigmaRegular_twistedOrbitMap hσ (lift T) (hlift T) x
    exact hfr.smul_measure (by simp)
  have hp (T : S) : Measurable (p T) :=
    T.val.measurable_twistedOrbitMap_of_branches hσ (lift T) (hlift T) (hlocal T)
  let H (T : S) (t : T.val.regularNormPoints σ l) :=
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
  let J (T : S) := T.val.twistedOrbitIntegrand hσ (lift T) (hlift T) (ν T) (w T) f
  have hJInt (T : S) : Integrable (J T) (τ T) := (hFubini T).2.1.smul (c T).toReal
  have hJBound (T : S) : (∫ t, ‖J T t‖ ∂τ T) ≤ ∫ g, ‖f g‖ ∂μpart T := by
    change (∫ t, ‖(c T).toReal • H T t‖ ∂τ T) ≤
      ∫ g, ‖f g‖ ∂c T • (ρ T).map (p T)
    have heq (t : T.val.regularNormPoints σ l) :
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
    change (∫ d, f d ∂c T • (ρ T).map (p T)) =
      ∫ t, (c T).toReal • H T t ∂τ T
    rw [integral_smul_measure, integral_map (hp T).aemeasurable (hfmap T).aestronglyMeasurable,
      (hFubini T).2.2.1, integral_smul]

end Langlands.BaseChange
