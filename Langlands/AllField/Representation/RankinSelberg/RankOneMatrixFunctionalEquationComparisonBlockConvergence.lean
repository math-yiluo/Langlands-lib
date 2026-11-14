import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBlockConvergence
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonBoxConvergence
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonPositiveAssembly
/-! # Absolute convergence of the actual rank-one-pair block integrals

A finite pointwise Schwartz expansion, with model vectors in the original
coefficient image, turns every block integrand into a finite sum of products
of zero-row integrands and compactly supported rectangular tests.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero singleton_modulus_real unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis hiding PadicRowFourierSurjectivityStatement PadicSelfDualMeasureExistsStatement padicLatticeGeometry padicRectangularHaarScaling padicRowFourierSurjectivity padicScalarHaarScaling padicSelfDualMeasureExists
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding MirabolicUnitTestStatement mirabolicUnitTest modelKirillovTransfer smoothSimpleRootSupport
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding padic_exists_ne_zero_mem_nhds_zero
open Langlands.AllField.GeneralLinear
open Langlands.QuotientIntegration

universe uF uV uX

namespace RankOneBlockConvergence
open Langlands.RankinSelberg.RankOneBlockConvergence hiding AllBlocksConvergeOnRight allBlocksConvergeOnRight_of_matrix blockConvergenceGLBorel blockConvergenceGLMeasurable blockConvergenceGLSigmaCompact blockConvergenceLocalField blockConvergenceQuotientBorel blockConvergenceQuotientMeasurable blockConvergenceScalarBorel blockConvergenceScalarMeasurable blockConvergenceSecondCountable blockConvergenceTopology blockConvergenceUnipotentBorel blockConvergenceUnipotentMeasurable blockConvergenceValuativeRel convergesOnRight_of_matrix converges_of_diagonal_integrable converges_of_finite_expansion integrable_quotient_prod_iff
open Langlands.AllField.RankinSelberg.RankOneBlockConvergence
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LastRowCompactOrbitStatement PadicPairGammaConstructionInput PadicPairGammaInput PadicSymmetricGammaConstructionInput PadicSymmetricGammaInput QuotientHaarExistenceStatement RankOneCharacterReductionStatement RankOneMatrixWhittakerComparisonStatement RankOneWhittakerTypeStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map diagonal_abs_bound diagonal_abs_last exists_rankOneCutoff exists_rankOneEmbedding_support glCoefficientModel_isOfWhittakerType isEqualRankLPolynomial_characterChange_normalized isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt lastRowCompactOrbit matrixComparisonModelsTopology matrixComparisonPositiveBorel matrixComparisonPositiveDisconnected matrixComparisonPositiveGLBorel matrixComparisonPositiveGLMeasurable matrixComparisonPositiveLocalField matrixComparisonPositiveMeasurable matrixComparisonPositiveQuotientBorel matrixComparisonPositiveQuotientMeasurable matrixComparisonPositiveT2 matrixComparisonPositiveTopology matrixComparisonPositiveUnipotentBorel matrixComparisonPositiveUnipotentMeasurable matrixComparisonPositiveValuation normalizedAbs_prod normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow padicPairGammaConstructionInput_iff padicPairGammaFactor padicPairGammaFactorOfWhittakerType padicSymmetricGammaConstructionInput_iff padicSymmetricGammaFactor padicSymmetricGammaFactorOfWhittakerType rankOneCharacterReduction rankOneCharacter_isOfWhittakerType rankOneGammaFactor_of_blockZero_one rankOneGammaFactor_of_normalized_blockZero_one rankOneMatrixWhittakerComparison_zero rankOneModelValues_subset_whittakerRationalValues rankOneWhittakerType rankOne_blockZero_exists_ne_zero singleton_modulus_real unequalRankCompactSupport unequalRankFiniteExpansion unequalRankGammaPropagation unequalRankIwasawaSupport unequalRankUnitSpan zeroRowLastRowCutoff zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance blockConvergenceSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance blockConvergenceScalarMeasurable : MeasurableSpace F := borel _
local instance blockConvergenceScalarBorel : BorelSpace F := ⟨rfl⟩
local instance blockConvergenceGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (n + 1) F) := borel _
local instance blockConvergenceGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
local instance blockConvergenceGLSigmaCompact (n : ℕ) :
    SigmaCompactSpace (Langlands.GeneralLinear (n + 1) F) :=
  (⟨⟩ : LocalFieldData F).generalLinearSigmaCompactSpace (n + 1)
local instance blockConvergenceUnipotentMeasurable :
    MeasurableSpace (upperUnipotent (0 + 1) F) := borel _
local instance blockConvergenceUnipotentBorel :
    BorelSpace (upperUnipotent (0 + 1) F) := ⟨rfl⟩
local instance blockConvergenceQuotientMeasurable :
    MeasurableSpace (LeftUnipotentQuotient 0 F) := borel _
local instance blockConvergenceQuotientBorel :
    BorelSpace (LeftUnipotentQuotient 0 F) := ⟨rfl⟩

/-- The actual rank-one quotient homeomorphism also transports a product
with any supplied s-finite rectangular measure. -/
theorem integrable_quotient_prod_iff {X : Type uX} [MeasurableSpace X]
    (ρ : Measure X) [SFinite ρ]
    (f : LeftUnipotentQuotient 0 F × X → ℂ) :
    Integrable f ((rankOneQuotientHaar F).prod ρ) ↔
      Integrable (fun gx : Langlands.GeneralLinear (0 + 1) F × X =>
        f (Quotient.mk _ gx.1, gx.2)) ((generalLinearHaar F 0).prod ρ) := by
  let e := (rankOneQuotientHomeomorph (F := F)).symm.toMeasurableEquiv.prodCongr (MeasurableEquiv.refl X)
  have he : ((rankOneQuotientHaar F).prod ρ) =
      Measure.map e ((generalLinearHaar F 0).prod ρ) := by
    have hef : (e : (Langlands.GeneralLinear (0 + 1) F × X) →
        LeftUnipotentQuotient 0 F × X) =
        Prod.map (rankOneQuotientHomeomorph (F := F)).symm (id : X → X) := by
      funext gx
      rfl
    rw [hef]
    have h := Measure.map_prod_map (generalLinearHaar F 0) ρ
      (rankOneQuotientHomeomorph (F := F)).symm.continuous.measurable (measurable_id : Measurable (id : X → X))
    simpa only [Measure.map_id, rankOneQuotientHaar] using h
  rw [he]
  exact integrable_map_equiv e f

section FixedShape

variable (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  {j k : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (0 + (j + k + 1) + 1) F) V)
  (ℓ : glFunctionals ψ (0 + (j + k + 1)) σ)

/-- A finite pointwise Schwartz expansion and convergence of every diagonal
model restriction imply absolute product convergence of the actual block. -/
theorem converges_of_finite_expansion (s : ℂ)
    (f : (coefficientModel σ ℓ).toSubmodule)
    (hbase : ∀ v : (coefficientModel σ ℓ).toSubmodule,
      Integrable (fun g => v.val.val (appendIdentity 0 (j + k + 1) g) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
          (s - ((j + k + 1 : ℕ) : ℂ) / 2)) (generalLinearHaar F 0))
    {d : ℕ} (φ : Fin d → SchwartzBruhat (Matrix (Fin j) (Fin (0 + 1)) F))
    (fs : Fin d → (coefficientModel σ ℓ).toSubmodule)
    (hexp : ∀ g X, f.val.val (unequalRankMatrix j k g X) =
      ∑ i : Fin d, φ i X * (fs i).val.val (appendIdentity 0 (j + k + 1) g)) :
    UnequalRankConverges ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) j k
      (rankOneQuotientHaar F) (rectangularMeasure ν j (0 + 1))
      f.val (rankOneTrivialModelOne ψ).val s := by
  rw [UnequalRankConverges, integrable_quotient_prod_iff F]
  have hi : ∀ i : Fin d, Integrable
      (fun gx : Langlands.GeneralLinear (0 + 1) F ×
          Matrix (Fin j) (Fin (0 + 1)) F =>
        ((fs i).val.val (appendIdentity 0 (j + k + 1) gx.1) *
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) gx.1
            (s - ((j + k + 1 : ℕ) : ℂ) / 2)) * φ i gx.2)
      ((generalLinearHaar F 0).prod (rectangularMeasure ν j (0 + 1))) := by
    intro i
    exact (hbase (fs i)).mul_prod
      ((φ i).continuous.integrable_of_hasCompactSupport (φ i).hasCompactSupport)
  have hsum := integrable_finsetSum (s := Finset.univ) (fun i _ => hi i)
  refine hsum.congr (Filter.Eventually.of_forall fun gx => ?_)
  dsimp only
  rw [unequalRankIntegrand_mk, rankOneTrivialModelOne_apply, mul_one, hexp, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Full Whittaker type gives the exact finite expansion used above. -/
theorem converges_of_diagonal_integrable
    (hσ : IsOfWhittakerType (0 + (j + k + 1))
      (standardCharacter ψ (0 + (j + k + 1))) σ) (hℓ : ℓ.val ≠ 0)
    (s : ℂ) (f : (coefficientModel σ ℓ).toSubmodule)
    (hbase : ∀ v : (coefficientModel σ ℓ).toSubmodule,
      Integrable (fun g => v.val.val (appendIdentity 0 (j + k + 1) g) *
        determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
          (s - ((j + k + 1 : ℕ) : ℂ) / 2)) (generalLinearHaar F 0)) :
    UnequalRankConverges ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) j k
      (rankOneQuotientHaar F) (rectangularMeasure ν j (0 + 1))
      f.val (rankOneTrivialModelOne ψ).val s := by
  have hs := unequalRankCompactSupport F (⟨⟩ : LocalFieldData F) 0 j k ψ V σ hσ ℓ hℓ f
  obtain ⟨d, φ, fs, hexp⟩ := unequalRankFiniteExpansion F (⟨⟩ : LocalFieldData F)
    0 j k ψ V σ hσ ℓ hℓ f hs
  exact converges_of_finite_expansion F ψ ν σ ℓ s f hbase φ fs hexp

end FixedShape

section AnyBlock

variable (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
  {r : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (σ : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (ℓ : glFunctionals ψ r σ)

/-- Absolute convergence of every allowed block with the canonical second
vector and a specified quotient measure, each on a right half-plane. -/
def AllBlocksConvergeOnRight (μ : Measure (LeftUnipotentQuotient 0 F)) : Prop :=
  ∀ (j k : ℕ) (hr : r = 0 + (j + k + 1)),
    ∃ b : ℝ, ∀ f : (coefficientModel σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
        UnequalRankConverges ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) j k
          μ (rectangularMeasure ν j (0 + 1))
          (InducedTailIntermediate.whittakerRankCast ψ hr f.val)
          (rankOneTrivialModelOne ψ).val s

/-- The supplied matrix convergence gives absolute convergence on a right
half-plane for every actual block and canonical-vector pair. -/
theorem convergesOnRight_of_matrix
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0)
    (hMatrix : Langlands.AllField.GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ))
    (j k : ℕ) (hr : r = 0 + (j + k + 1)) :
    ∃ b : ℝ, ∀ f : (coefficientModel σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re →
      UnequalRankConverges ψ (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) j k
        (rankOneQuotientHaar F) (rectangularMeasure ν j (0 + 1))
        (InducedTailIntermediate.whittakerRankCast ψ hr f.val)
        (rankOneTrivialModelOne ψ).val s := by
  subst r
  have hbase : ∃ b : ℝ, ∀ v : (coefficientModel σ ℓ).toSubmodule,
      ∀ s : ℂ, b < s.re → Integrable
        (fun g => v.val.val (appendIdentity 0 (j + k + 1) g) *
          determinantWeight (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)) g
            (s - ((j + k + 1 : ℕ) : ℂ) / 2)) (generalLinearHaar F 0) := by
    obtain ⟨b, hb⟩ := Langlands.AllField.RankinSelberg.RankOneBox.rankOneModel_convergesOnRight_of_matrix
      F ψ σ ℓ hσ.1.1 hMatrix
    refine ⟨b, fun v s hs => ?_⟩
    have h := hb v s hs
    convert h using 1
    funext g
    have hg : appendIdentity 0 (j + k + 1) g = rankOneEmbedding (0 + (j + k)) g := by
      apply Units.ext
      rw [rankOneEmbedding_val]
      ext a b
      cases a using Fin.cases <;> cases b using Fin.cases <;>
        simp [appendIdentity_entry, Matrix.diagonal_apply, eq_comm]
    rw [hg]
    simp only [rankOneModelIntegrand, glModelFunction]
    congr 2
    have hn : Nat.add 0 (j + k) = j + k := Nat.zero_add _
    rw [hn]
  obtain ⟨b, hb⟩ := hbase
  exact ⟨b, fun f s hs => converges_of_diagonal_integrable F ψ ν σ ℓ hσ hℓ s f
    (fun v => hb v s hs)⟩

/-- The actual matrix convergence supplies absolute convergence of all blocks
for every compatible rank-one quotient measure. -/
theorem allBlocksConvergeOnRight_of_matrix
    (hσ : IsOfWhittakerType r (standardCharacter ψ r) σ) (hℓ : ℓ.val ≠ 0)
    (μ : Measure (LeftUnipotentQuotient 0 F))
    (hμ : IsCompatible (upperUnipotent (0 + 1) F) (generalLinearHaar F 0)
      (unipotentHaar F 0) μ)
    (hMatrix : Langlands.AllField.GodementJacquet.Padic.MatrixConvergesOnRight F
      (V := (glCoefficientModel ψ r σ ℓ).toSubmodule) (glModelRepresentation ψ r σ ℓ)) :
    AllBlocksConvergeOnRight F ψ ν σ ℓ μ := by
  rw [eq_rankOneQuotientHaar_of_isCompatible F μ hμ]
  exact convergesOnRight_of_matrix F ψ ν σ ℓ hσ hℓ hMatrix

end AnyBlock

end RankOneBlockConvergence

end Langlands.AllField.RankinSelberg
