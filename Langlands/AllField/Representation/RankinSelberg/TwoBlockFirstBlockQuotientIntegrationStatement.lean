import Langlands.Representation.RankinSelberg.TwoBlockFirstBlockQuotientIntegrationStatement
import Langlands.AllField.Representation.RankinSelberg.TwoBlockFirstBlockQuotientData
/-!
# Normalized first-block quotient integration on determinant slices

Analytic statement underlying JPSS (1983), Section 4.6, printed page 412, equation (6):

`∫_{N_(t_1,t_2) \ G_r^m} f(g) dg =
  ∫_{G_(t_1)^0 N_(t_1,t_2) \ G_r^0} dh ∫_{N_(t_1) \ G_(t_1)^m} f[diag(a, 1) h] d^×a`.

The subgroups, quotients, slices, fiber map and first-block average are the published actual
objects of `TwoBlockFirstBlockQuotientData`. The ambient and subgroup measures are the
published normalized Haar measures, with the Haar measure of `GL_a^0` given by restriction
from `GL_a`; no factor occurs. The kernel packaging and the absolute-integrability
equivalence are derived consequences of the source formula. This module states, but does
not prove, these assertions.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt TwoBlockFirstBlockQuotientIntegrationStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.GeneralLinear
open Langlands.QuotientIntegration
open scoped ENNReal ProbabilityTheory

universe uF

/-- Normalized disintegration of `H \ G^k` over the zero slice `L \ G^0`, where
`H = N_(t_1,t_2)` is the block-diagonal unipotent subgroup and
`L = diag(GL_a^0, N_b)`, with fibers the small slices `N_a \ GL_a^k` through
`[u] ↦ [diag(u, 1) g]_H`. The measures are the published normalized Haar measures; the
Haar measure of `GL_a^0` is the restriction of that of `GL_a`. The conclusions include
compatible quotient existence, sigma-finiteness, a measurable s-finite fiber kernel for each
`k`, the restricted measure and Tonelli identities, and absolute-integrability and Bochner
laws for the published first-block average. -/
def TwoBlockFirstBlockQuotientIntegrationStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
    (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1),
    let T := (⟨⟩ : LocalFieldData F)
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI := T.fieldT2
    letI := T.secondCountableTopology
    letI := T.generalLinearTopologicalGroup (t + 1)
    letI := T.generalLinearTopologicalGroup (m 0 + 1)
    letI : MeasurableSpace F := borel F
    letI : BorelSpace F := ⟨rfl⟩
    let G := GeneralLinear (t + 1) F
    let GA := GeneralLinear (m 0 + 1) F
    let Na := upperUnipotent (m 0 + 1) F
    let Nb := upperUnipotent (m 1 + 1) F
    let A0 := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneSubgroup F (m 0 + 1)
    let H := TwoBlockUnipotentQuotient.blockUnipotent h F
    let L := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroup F h
    let AQ := LeftUnipotentQuotient (m 0) F
    let HQ := TwoBlockUnipotentQuotient.BlockQuotient h F
    let LQ := Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.MixedQuotient F h
    letI : SecondCountableTopology GA := T.generalLinearSecondCountableTopology (m 0 + 1)
    letI : MeasurableSpace G := borel G
    letI : BorelSpace G := ⟨rfl⟩
    letI : MeasurableSpace GA := borel GA
    letI : BorelSpace GA := ⟨rfl⟩
    letI : MeasurableSpace A0 := borel A0
    letI : BorelSpace A0 := ⟨rfl⟩
    letI : SecondCountableTopology A0 := Topology.IsEmbedding.subtypeVal.secondCountableTopology
    letI : MeasurableSpace H := borel H
    letI : BorelSpace H := ⟨rfl⟩
    letI : MeasurableSpace L := borel L
    letI : BorelSpace L := ⟨rfl⟩
    letI : ∀ i : Fin 2, MeasurableSpace (upperUnipotent (m i + 1) F) :=
      fun i => borel (upperUnipotent (m i + 1) F)
    letI : ∀ i : Fin 2, BorelSpace (upperUnipotent (m i + 1) F) :=
      fun _ => ⟨rfl⟩
    letI : ∀ i : Fin 2, SecondCountableTopology (upperUnipotent (m i + 1) F) :=
      fun i => by
        let := T.generalLinearSecondCountableTopology (m i + 1)
        exact Topology.IsEmbedding.subtypeVal.secondCountableTopology
    -- These Borel instances use the actual finite product measurable spaces.
    letI : BorelSpace (TwoBlockUnipotentQuotient.BlockUnipotents m F) := inferInstance
    letI : BorelSpace (A0 × Nb) := inferInstance
    letI : MeasurableSpace AQ := borel AQ
    letI : BorelSpace AQ := ⟨rfl⟩
    letI : MeasurableSpace HQ := borel HQ
    letI : BorelSpace HQ := ⟨rfl⟩
    letI : MeasurableSpace LQ := borel LQ
    letI : BorelSpace LQ := ⟨rfl⟩
    let μG : Measure G := generalLinearHaar F t
    let μGA : Measure GA := generalLinearHaar F (m 0)
    let μNa : Measure Na := unipotentHaar F (m 0)
    let μNb : Measure Nb := unipotentHaar F (m 1)
    let μH : Measure H := Measure.map (TwoBlockUnipotentQuotient.blockUnipotentEquiv h F)
      (Measure.pi (fun i : Fin 2 => unipotentHaar F (m i)))
    μH.IsHaarMeasure ∧ μH.Regular ∧
      ∃ μA0 : Measure A0, μA0.IsHaarMeasure ∧ μA0.Regular ∧
        Measure.map Subtype.val μA0 = μGA.restrict (A0 : Set GA) ∧
        let μL : Measure L :=
          Measure.map (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.mixedSubgroupEquiv F h) (μA0.prod μNb)
        μL.IsHaarMeasure ∧ μL.Regular ∧
          ∃ (hNa : Measure.IsMulRightInvariant μNa) (hH : Measure.IsMulRightInvariant μH)
            (hL : Measure.IsMulRightInvariant μL),
            letI := hNa
            letI := hH
            letI := hL
            (∃ νA : Measure AQ, IsCompatible Na μGA μNa νA) ∧
            (∃ νH : Measure HQ, IsCompatible H μG μH νH) ∧
            (∃ νL : Measure LQ, IsCompatible L μG μL νL) ∧
            ∀ (νA : Measure AQ) (νH : Measure HQ) (νL : Measure LQ)
              (hA : IsCompatible Na μGA μNa νA),
              IsCompatible H μG μH νH → IsCompatible L μG μL νL →
              SigmaFinite νA ∧ SigmaFinite νH ∧ SigmaFinite νL ∧
              ∀ k : ℤ,
                let hInvariant :=
                  Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.normOneRightInvariant_of_isCompatible F (m 0)
                    μGA μNa νA hA
                let νL0 := νL.restrict (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.determinantSlice F h 0)
                let νHk := νH.restrict (Langlands.AllField.RankinSelberg.TwoBlockUnipotentQuotient.determinantSlice F h k)
                ∃ (κ : ProbabilityTheory.Kernel LQ HQ)
                  (_hκ : ProbabilityTheory.IsSFiniteKernel κ),
                  (∀ g : G, κ (Quotient.mk _ g) =
                    Measure.map (fun q => TwoBlockFirstBlockQuotient.fiberPoint h F q g)
                      (νA.restrict (Langlands.AllField.RankinSelberg.determinantSlice T (m 0) k))) ∧
                  (κ ∘ₘ νL0 = νHk) ∧
                  (∀ f : HQ → ℝ≥0∞, Measurable f →
                    (∫⁻ q, ∫⁻ z, f z ∂κ q ∂νL0) = ∫⁻ z, f z ∂νHk) ∧
                  (∀ f : HQ → ℂ, Measurable f →
                    (Integrable f νHk ↔
                      (∀ᵐ q ∂νL0, Integrable f (κ q)) ∧
                      Integrable (fun q => ∫ z, ‖f z‖ ∂κ q) νL0) ∧
                    (Integrable f νHk →
                      Integrable
                        (Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInvariant k f)
                        νL0 ∧
                      (∫ z, f z ∂νHk) =
                        ∫ q, Langlands.AllField.RankinSelberg.TwoBlockFirstBlockQuotient.firstBlockAverage F h νA hInvariant k f q
                          ∂νL0))

end Langlands.AllField.RankinSelberg
