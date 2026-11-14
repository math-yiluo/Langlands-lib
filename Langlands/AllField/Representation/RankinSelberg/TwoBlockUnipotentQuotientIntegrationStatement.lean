import Langlands.Representation.RankinSelberg.TwoBlockUnipotentQuotientIntegrationStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockUnipotentQuotientData
/-!
# Normalized integration for the two-block unipotent quotient tower

Derived analytic infrastructure for the first unfolding of JPSS (1983),
Section 4.6, printed pages 411-412. The subgroup and quotient maps are the
published actual objects. The rectangular additive Haar measure is supplied
unchanged, with its integral-cube mass retained as the factor in the measure,
Tonelli and Bochner identities. This module states, but does not prove, the
quotient-measure existence, fiber-kernel and absolute-integrability assertions.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockUnipotentQuotientIntegrationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open Langlands.RankinSelberg.TwoBlockUnipotentQuotient hiding continuous_fiberPoint continuous_projection determinantSlice fiberIntegral fiberIntegral_def fiberIntegral_upperUnipotent_mul iUnion_determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice pairwise_disjoint_determinantSlice radicalAverage radicalAverage_mk
open Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient hiding determinantSlice isClopen_determinantSlice measurableSet_determinantSlice mk_mem_determinantSlice
open scoped ENNReal ProbabilityTheory

universe uF

/-- Normalized integration along `H \\ G → N \\ G`, where `H` is the block-diagonal
unipotent subgroup, for every supplied rectangular additive Haar measure.
The factor is its positive finite integral-cube mass. The conclusions include
compatible quotient existence, a measurable s-finite fiber kernel, restricted
measure and Tonelli identities, and absolute-integrability and Bochner laws. -/
def TwoBlockUnipotentQuotientIntegrationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1),
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.secondCountableTopology
    letI := T.generalLinearTopologicalGroup (t + 1)
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    let G := GeneralLinear (t + 1) F
    let N := upperUnipotent (t + 1) F
    let H := blockUnipotent h F
    let NQ := LeftUnipotentQuotient t F
    let HQ := BlockQuotient h F
    let R := Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace N := borel N
    letI : BorelSpace N := ⟨rfl⟩
    letI : MeasurableSpace H := borel H
    letI : BorelSpace H := ⟨rfl⟩
    letI : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F) :=
      fun i => borel (upperUnipotent (m i + 1) F)
    letI : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F) :=
      fun _ => ⟨rfl⟩
    letI : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F) :=
      fun i => by
        let := T.generalLinearSecondCountableTopology (m i + 1)
        exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    -- These Borel instances use the actual finite product measurable spaces.
    letI : BorelSpace (BlockUnipotents m F) := inferInstance
    letI : BorelSpace R := inferInstance
    letI : MeasurableSpace NQ := borel NQ
    letI : BorelSpace NQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    let μG : Measure G := generalLinearHaar F t
    let μN : Measure N := unipotentHaar F t
    let μH : Measure H := Measure.map (blockUnipotentEquiv h F)
      (Measure.pi (fun i : Fin 2 => unipotentHaar F (m i)))
    μH.IsHaarMeasure ∧ μH.Regular ∧
      ∃ (hN : Measure.IsMulRightInvariant μN) (hH : Measure.IsMulRightInvariant μH),
        letI := hN
        letI := hH
        (∃ νN : Measure NQ, IsCompatible N μG μN νN) ∧
        (∃ νH : Measure HQ, IsCompatible H μG μH νH) ∧
        ∀ (μR : Measure R) [μR.IsAddHaarMeasure],
          let O := (ValuativeRel.valuation F).integer
          let c : ℝ≥0∞ := μR {x | ∀ a b, x a b ∈ O}
          0 < c ∧ c < ⊤ ∧
            ∃ (κ : ProbabilityTheory.Kernel NQ HQ)
              (_hκ : ProbabilityTheory.IsSFiniteKernel κ),
              (∀ g : G, κ (Quotient.mk _ g) =
                Measure.map (fun x => fiberPoint h F x g) μR) ∧
              ∀ (νN : Measure NQ) (νH : Measure HQ),
                IsCompatible N μG μN νN → IsCompatible H μG μH νH →
                SigmaFinite νN ∧ SigmaFinite νH ∧
                ∀ s : Set NQ, MeasurableSet s →
                  let νNs := νN.restrict s
                  let νHs := νH.restrict (projection h F ⁻¹' s)
                  (κ ∘ₘ νNs = c • νHs) ∧
                  (∀ f : HQ → ℝ≥0∞, Measurable f →
                    (∫⁻ q, ∫⁻ z, f z ∂κ q ∂νNs) = c * ∫⁻ z, f z ∂νHs) ∧
                  (∀ f : HQ → ℂ, Measurable f →
                    (Integrable f νHs ↔
                      (∀ᵐ q ∂νNs, Integrable f (κ q)) ∧
                      Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) νNs) ∧
                    (Integrable f νHs →
                      Integrable (radicalAverage F h μR f) νNs ∧
                      (∫ q, radicalAverage F h μR f q ∂νNs) =
                        c.toReal • (∫ z, f z ∂νHs)))

end Langlands.AllField.RankinSelberg
