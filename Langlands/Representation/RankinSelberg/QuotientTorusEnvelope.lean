import Langlands.Representation.RankinSelberg.QuotientIwasawaIntegrationProof
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! Summable torus envelopes for the actual standard unipotent quotient. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Langlands.RankinSelberg.QuotientTorusEnvelope

open GeneralLinear QuotientIntegration

universe uF

/-- A summable bound on probability pushforwards gives genuine integrability
for their weighted countable sum. -/
theorem integrable_sum_smul_map_of_bound
    {L X Y : Type*} [Countable L] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (q : L → X → Y) (hq : ∀ l, Measurable (q l))
    (E : Y → ℂ) (hE : Measurable E)
    (c A : L → ℝ) (hc : ∀ l, 0 ≤ c l)
    (hbound : ∀ l, ∀ᵐ x ∂ν, ‖E (q l x)‖ ≤ A l)
    (hsum : Summable (fun l => c l * A l)) :
    Integrable E (Measure.sum (fun l => ENNReal.ofReal (c l) • Measure.map (q l) ν)) := by
  have hcomp (l : L) : Integrable (fun x => E (q l x)) ν :=
    Integrable.of_bound (hE.comp (hq l)).aestronglyMeasurable (A l) (hbound l)
  have hmap (l : L) : Integrable E (Measure.map (q l) ν) :=
    (integrable_map_measure hE.aestronglyMeasurable (hq l).aemeasurable).2 (hcomp l)
  have hi (l : L) :
      Integrable E (ENNReal.ofReal (c l) • Measure.map (q l) ν) :=
    (hmap l).smul_measure ENNReal.ofReal_ne_top
  apply integrable_sum_measure hi
  apply Summable.of_nonneg_of_le (fun l => integral_nonneg (fun _ => norm_nonneg _)) _ hsum
  intro l
  rw [integral_smul_measure, ENNReal.toReal_ofReal (hc l), smul_eq_mul,
    integral_map (hq l).aemeasurable hE.norm.aestronglyMeasurable]
  apply mul_le_mul_of_nonneg_left _ (hc l)
  calc
    (∫ x, ‖E (q l x)‖ ∂ν) ≤ ∫ _x, A l ∂ν :=
      integral_mono_ae (hcomp l).norm (integrable_const _) (hbound l)
    _ = A l := by simp

/-- The actual `L¹` class constructed from a summable pushforward envelope. -/
def sumPushforwardL1
    {L X Y : Type*} [Countable L] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (q : L → X → Y) (hq : ∀ l, Measurable (q l))
    (E : Y → ℂ) (hE : Measurable E)
    (c A : L → ℝ) (hc : ∀ l, 0 ≤ c l)
    (hbound : ∀ l, ∀ᵐ x ∂ν, ‖E (q l x)‖ ≤ A l)
    (hsum : Summable (fun l => c l * A l)) :
    Y →₁[Measure.sum (fun l => ENNReal.ofReal (c l) • Measure.map (q l) ν)] ℂ :=
  (integrable_sum_smul_map_of_bound ν q hq E hE c A hc hbound hsum).toL1 E

/-- Passing to the constructed `L¹` class preserves the supplied function
almost everywhere for the weighted sum measure. -/
theorem sumPushforwardL1_coe
    {L X Y : Type*} [Countable L] [MeasurableSpace X] [MeasurableSpace Y]
    (ν : Measure X) [IsProbabilityMeasure ν]
    (q : L → X → Y) (hq : ∀ l, Measurable (q l))
    (E : Y → ℂ) (hE : Measurable E)
    (c A : L → ℝ) (hc : ∀ l, 0 ≤ c l)
    (hbound : ∀ l, ∀ᵐ x ∂ν, ‖E (q l x)‖ ≤ A l)
    (hsum : Summable (fun l => c l * A l)) :
    (sumPushforwardL1 ν q hq E hE c A hc hbound hsum : Y → ℂ) =ᵐ[
      Measure.sum (fun l => ENNReal.ofReal (c l) • Measure.map (q l) ν)] E :=
  (integrable_sum_smul_map_of_bound ν q hq E hE c A hc hbound hsum).coeFn_toL1

/-- The literal inverse upper-Borel modulus on a uniformizer exponent vector. -/
def density {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (ϖ : F.Carrierˣ) (lam : Fin (n + 1) → ℤ) : ℝ :=
  (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
    T.normalizedAbs (((ϖ ^ lam i) / (ϖ ^ lam j) : F.Carrierˣ) : F.Carrier))⁻¹

theorem density_pos {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (T : F.TopologicalData) {n : ℕ} (ϖ : F.Carrierˣ) (lam : Fin (n + 1) → ℤ) :
    0 < density F T ϖ lam := by
  apply inv_pos.mpr
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact T.normalizedAbs_pos (Units.ne_zero _)

/-- Every compatible quotient measure is the sum of the mass-one compact
pushforwards with the exact inverse-modulus weights. -/
theorem quotientMeasure_eq_sum_torus {p : ℕ} [Fact p.Prime]
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
      μ = Measure.sum (fun lam : Fin (n + 1) → ℤ =>
        ENNReal.ofReal (density F T ϖ lam) •
          Measure.map
            (fun k => leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
              (Iwasawa.torus ϖ lam * k))
            ((generalLinearHaar F.Carrier n).restrict
              (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
                Set _))) := by
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
  intro _ μ hμ ϖ hϖ
  exact (quotientIwasawaIntegration F T n μ hμ).trans
    (iwasawaTorusSum p F T n ϖ hϖ)

/-- A measurable complex function with a summable torus envelope is absolutely
integrable for every compatible standard quotient measure. -/
theorem integrable_of_summable_torus_bound {p : ℕ} [Fact p.Prime]
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
      ∀ (E : LeftUnipotentQuotient n F.Carrier → ℂ), Measurable E →
      ∀ A : (Fin (n + 1) → ℤ) → ℝ,
        (∀ lam k,
          k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n →
          ‖E (leftQuotientMap (upperUnipotent (n + 1) F.Carrier)
            (Iwasawa.torus ϖ lam * k))‖ ≤ A lam) →
        Summable (fun lam => density F T ϖ lam * A lam) →
        Integrable E μ := by
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
  intro _ μ hμ ϖ hϖ E hE A hbound hsum
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
  have hK : MeasurableSet (K : Set G) := by
    change MeasurableSet
      (Conductor.integralSubgroup (ValuativeRel.valuation F.Carrier).integer n : Set G)
    rw [← Conductor.levelSubgroup_zero F.Carrier n]
    exact (Conductor.levelOpenSubgroup F.Carrier n 0).isOpen.measurableSet
  have hq (lam : Fin (n + 1) → ℤ) : Measurable (q lam) :=
    ((leftQuotient_isOpenQuotientMap _).continuous.comp
      (continuous_const.mul continuous_id)).measurable
  rw [quotientMeasure_eq_sum_torus F T n μ hμ ϖ hϖ]
  apply integrable_sum_smul_map_of_bound ν q hq E hE
    (density F T ϖ) A (fun lam => (density_pos F T ϖ lam).le) _ hsum
  intro lam
  filter_upwards [ae_restrict_mem hK] with k hk
  exact hbound lam k hk

end Langlands.RankinSelberg.QuotientTorusEnvelope
