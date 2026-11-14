import Langlands.Representation.RankinSelberg.QuotientTorusEnvelope
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.RankinSelberg.QuotientIwasawaIntegrationProof
/-! Summable torus envelopes for the actual standard unipotent quotient. -/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Langlands.AllField.RankinSelberg.QuotientTorusEnvelope
open Langlands.RankinSelberg.QuotientTorusEnvelope hiding density density_pos integrable_of_summable_torus_bound quotientMeasure_eq_sum_torus
open Langlands.AllField.RankinSelberg.QuotientTorusEnvelope
open Langlands.RankinSelberg hiding QuotientIwasawaIntegrationStatement diagonalConj_map iwasawaTorusSum quotientIwasawaIntegration singleton_modulus_real
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.QuotientIntegration

universe uF

/-- The literal inverse upper-Borel modulus on a uniformizer exponent vector. -/
def density (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (ϖ : Fˣ) (lam : Fin (n + 1) → ℤ) : ℝ :=
  (∏ i : Fin (n + 1), ∏ j ∈ Finset.univ.filter (fun j : Fin (n + 1) => i < j),
    T.normalizedAbs (((ϖ ^ lam i) / (ϖ ^ lam j) : Fˣ) : F))⁻¹

theorem density_pos (F : Type uF) [Field F]
    (T : LocalFieldData F) {n : ℕ} (ϖ : Fˣ) (lam : Fin (n + 1) → ℤ) :
    0 < density F T ϖ lam := by
  apply inv_pos.mpr
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j _
  exact T.normalizedAbs_pos (Units.ne_zero _)

/-- Every compatible quotient measure is the sum of the mass-one compact
pushforwards with the exact inverse-modulus weights. -/
theorem quotientMeasure_eq_sum_torus 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)]
      (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ ϖ : Fˣ,
        Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ →
      μ = Measure.sum (fun lam : Fin (n + 1) → ℤ =>
        ENNReal.ofReal (density F T ϖ lam) •
          Measure.map
            (fun k => leftQuotientMap (upperUnipotent (n + 1) F)
              (Iwasawa.torus ϖ lam * k))
            ((generalLinearHaar F n).restrict
              (Conductor.integralSubgroup (ValuativeRel.valuation F).integer n :
                Set _))) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro _ μ hμ ϖ hϖ
  exact (quotientIwasawaIntegration F T n μ hμ).trans
    (iwasawaTorusSum F T n ϖ hϖ)

/-- A measurable complex function with a summable torus envelope is absolutely
integrable for every compatible standard quotient measure. -/
theorem integrable_of_summable_torus_bound 
    (F : Type uF) [Field F] (T : LocalFieldData F) (n : ℕ) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := borel Fˣ
    letI : BorelSpace Fˣ := ⟨rfl⟩
    letI := borel (Langlands.GeneralLinear (n + 1) F)
    letI : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
    letI := borel (upperUnipotent (n + 1) F)
    letI : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
    letI := borel (LeftUnipotentQuotient n F)
    letI : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
    ∀ [Measure.IsMulRightInvariant (unipotentHaar F n)]
      (μ : Measure (LeftUnipotentQuotient n F)),
      IsCompatible (upperUnipotent (n + 1) F)
        (generalLinearHaar F n) (unipotentHaar F n) μ →
      ∀ ϖ : Fˣ,
        Iwasawa.IsUniformizingElement (ValuativeRel.valuation F) ϖ →
      ∀ (E : LeftUnipotentQuotient n F → ℂ), Measurable E →
      ∀ A : (Fin (n + 1) → ℤ) → ℝ,
        (∀ lam k,
          k ∈ Conductor.integralSubgroup (ValuativeRel.valuation F).integer n →
          ‖E (leftQuotientMap (upperUnipotent (n + 1) F)
            (Iwasawa.torus ϖ lam * k))‖ ≤ A lam) →
        Summable (fun lam => density F T ϖ lam * A lam) →
        Integrable E μ := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := borel Fˣ
  let : BorelSpace Fˣ := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro _ μ hμ ϖ hϖ E hE A hbound hsum
  let G := Langlands.GeneralLinear (n + 1) F
  let K := Conductor.integralSubgroup (ValuativeRel.valuation F).integer n
  let ν := (generalLinearHaar F n).restrict (K : Set G)
  let q := fun (lam : Fin (n + 1) → ℤ) (k : G) =>
    leftQuotientMap (upperUnipotent (n + 1) F) (Iwasawa.torus ϖ lam * k)
  have hν : ν Set.univ = 1 := by
    change (generalLinearHaar F n).restrict (K : Set G) Set.univ = 1
    rw [Measure.restrict_apply_univ]
    exact generalLinearHaar_integralSubgroup F n
  let : IsProbabilityMeasure ν := ⟨hν⟩
  have hK : MeasurableSet (K : Set G) := by
    change MeasurableSet
      (Conductor.integralSubgroup (ValuativeRel.valuation F).integer n : Set G)
    rw [← Conductor.levelSubgroup_zero F n]
    exact (Conductor.levelOpenSubgroup F n 0).isOpen.measurableSet
  have hq (lam : Fin (n + 1) → ℤ) : Measurable (q lam) :=
    ((leftQuotient_isOpenQuotientMap _).continuous.comp
      (continuous_const.mul continuous_id)).measurable
  rw [quotientMeasure_eq_sum_torus F T n μ hμ ϖ hϖ]
  apply integrable_sum_smul_map_of_bound ν q hq E hE
    (density F T ϖ) A (fun lam => (density_pos F T ϖ lam).le) _ hsum
  intro lam
  filter_upwards [ae_restrict_mem hK] with k hk
  exact hbound lam k hk

end Langlands.AllField.RankinSelberg.QuotientTorusEnvelope
