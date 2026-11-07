import Langlands.Representation.RankinSelberg.QuotientTorusEnvelope

/-! # Exact torus summation for spherical quotient functions -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Langlands.RankinSelberg.QuotientTorusEnvelope

open GeneralLinear QuotientIntegration

universe uF

/-- A measurable function constant on each probability fiber has its literal
weighted series as its integral, with absolute integrability proved by that series. -/
theorem integrable_integral_sum_smul_map_of_fiberConstant
    {L X Y : Type*} [Countable L] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (q : L → X → Y) (hq : ∀ l, Measurable (q l))
    (E : Y → ℂ) (hE : Measurable E)
    (c : L → ℝ) (hc : ∀ l, 0 ≤ c l) (H : L → ℂ)
    (hconst : ∀ l, ∀ᵐ x ∂ν, E (q l x) = H l)
    (hsum : Summable (fun l => c l * ‖H l‖)) :
    Integrable E (Measure.sum (fun l => ENNReal.ofReal (c l) • Measure.map (q l) ν)) ∧
      (∫ y, E y ∂Measure.sum (fun l => ENNReal.ofReal (c l) • Measure.map (q l) ν)) =
        ∑' l, (c l : ℂ) * H l := by
  have hi := integrable_sum_smul_map_of_bound ν q hq E hE c
    (fun l => ‖H l‖) hc (fun l => (hconst l).mono fun _ hx => by rw [hx]) hsum
  refine ⟨hi, ?_⟩
  rw [integral_sum_measure hi]
  apply tsum_congr
  intro l
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hc l),
    integral_map (hq l).aemeasurable hE.aestronglyMeasurable,
    integral_congr_ae (hconst l)]
  simp

/-- The literal weighted torus coefficient of a function on the actual quotient. -/
def torusCoefficient {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (ϖ : F.Carrierˣ)
    (E : LeftUnipotentQuotient n F.Carrier → ℂ) (lam : Fin (n + 1) → ℤ) : ℂ :=
  (density F T ϖ lam : ℂ) *
    E (leftQuotientMap (upperUnipotent (n + 1) F.Carrier) (Iwasawa.torus ϖ lam))

/-- Every compatible standard quotient measure gives exactly the torus series
for a measurable right-integral-invariant function with summable torus norms. -/
theorem integrable_integral_eq_tsum_torus {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel F.Carrierˣ
    letI : BorelSpace F.Carrierˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F.Carrier)
    letI : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F.Carrier)
    letI : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F.Carrier n)]
      (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
      IsCompatible (upperUnipotent (n + 1) F.Carrier)
        (generalLinearHaar F.Carrier n) (unipotentHaar F.Carrier n) μ →
      ∀ ϖ : F.Carrierˣ,
        Iwasawa.IsUniformizingElement (ValuativeRel.valuation F.Carrier) ϖ →
      ∀ E : LeftUnipotentQuotient n F.Carrier → ℂ, Measurable E →
        (∀ lam k,
          k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
          E (leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
            (Iwasawa.torus ϖ lam * k)) =
            E (leftQuotientMap (upperUnipotent (n + 1) F.Carrier) (Iwasawa.torus ϖ lam))) →
        Summable (fun lam => ‖torusCoefficient F T ϖ E lam‖) →
        Integrable E μ ∧ (∫ x, E x ∂μ) = ∑' lam, torusCoefficient F T ϖ E lam := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel F.Carrierˣ
  let : BorelSpace F.Carrierˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩
  intro _ μ hμ ϖ hϖ E hE hK hsum
  let G := Langlands.GeneralLinear (n + 1) F.Carrier
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n
  let ν := (generalLinearHaar F.Carrier n).restrict (K : Set G)
  let q := fun (lam : Fin (n + 1) → ℤ) (k : G) =>
    leftQuotientMap (upperUnipotent (n + 1) F.Carrier) (Iwasawa.torus ϖ lam * k)
  have hν : ν Set.univ = 1 := by
    change (generalLinearHaar F.Carrier n).restrict (K : Set G) Set.univ = 1
    rw [Measure.restrict_apply_univ]
    exact generalLinearHaar_integralSubgroup F.Carrier n
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hKm : MeasurableSet (K : Set G) := by
    change MeasurableSet
      (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n : Set G)
    rw [← Conductor.levelSubgroup_zero F.Carrier n]
    exact (Conductor.levelOpenSubgroup F.Carrier n 0).isOpen.measurableSet
  have hq (lam : Fin (n + 1) → ℤ) : Measurable (q lam) :=
    ((leftQuotient_isOpenQuotientMap _).continuous.comp
      (continuous_const.mul continuous_id)).measurable
  rw [quotientMeasure_eq_sum_torus F T n μ hμ ϖ hϖ]
  apply integrable_integral_sum_smul_map_of_fiberConstant ν q hq E hE
    (density F T ϖ) (fun lam => (density_pos F T ϖ lam).le)
  · intro lam
    filter_upwards [ae_restrict_mem hKm] with k hk
    exact hK lam k hk
  · simpa only [torusCoefficient, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (density_pos F T ϖ _)] using hsum

end Langlands.RankinSelberg.QuotientTorusEnvelope
