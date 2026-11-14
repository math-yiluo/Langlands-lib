import Langlands.Representation.RankinSelberg.TwoBlockUnipotentMeasures
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
/-!
# Fixed measures for the two-block unipotent quotient

The subgroup measure is exactly the transport of the two normalized block
unipotent Haar measures. Its invariance and regularity give compatible quotient
existence. The integral rectangular cube has positive finite mass for every
supplied additive Haar measure.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul integerCube_mass_pos_lt_top isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice radicalAverage radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg hiding determinantSlice iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice

open _root_.MeasureTheory TopologicalSpace
open Langlands.GeneralLinear hiding blockUnipotent
open Langlands.QuotientIntegration
open scoped ENNReal

universe uF

section BlockMeasure



end BlockMeasure

section FullUnipotentMeasure


end FullUnipotentMeasure

section Canonical

variable (F : Type uF) [Field F]
  {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

/-- Every supplied rectangular additive Haar gives the integral cube positive finite mass. -/
theorem integerCube_mass_pos_lt_top [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (a b : ℕ) :
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (μ : Measure (Matrix (Fin a) (Fin b) F)) [μ.IsAddHaarMeasure],
      0 < μ {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F).integer} ∧
        μ {x | ∀ i j, x i j ∈ (ValuativeRel.valuation F).integer} < ⊤ := by
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let := T.fieldT2
  let := T.secondCountableTopology
  let : MeasurableSpace F := borel F
  let : BorelSpace F := ⟨rfl⟩
  dsimp only
  intro μ _
  let O := (ValuativeRel.valuation F).integer
  have he : {x : Matrix (Fin a) (Fin b) F | ∀ i j, x i j ∈ O} =
      Set.univ.pi (fun _ : Fin a => Set.univ.pi (fun _ : Fin b => (O : Set F))) := by
    ext x
    change (∀ i j, x i j ∈ O) ↔
      (∀ i ∈ Set.univ, ∀ j ∈ Set.univ, x i j ∈ O)
    simp
  have hc : IsCompact {x : Matrix (Fin a) (Fin b) F | ∀ i j, x i j ∈ O} := by
    rw [he]
    exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => T.isCompact_integers
  have ho : IsOpen {x : Matrix (Fin a) (Fin b) F | ∀ i j, x i j ∈ O} := by
    rw [he]
    exact isOpen_set_pi Set.finite_univ fun _ _ =>
      isOpen_set_pi Set.finite_univ fun _ _ => T.isOpen_integers
  change 0 < μ {x | ∀ i j, x i j ∈ O} ∧ μ {x | ∀ i j, x i j ∈ O} < ⊤
  exact ⟨ho.measure_pos μ ⟨0, fun _ _ => O.zero_mem⟩, hc.measure_lt_top⟩

end Canonical

end Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient
