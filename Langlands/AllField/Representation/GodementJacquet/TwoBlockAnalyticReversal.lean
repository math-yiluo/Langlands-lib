import Langlands.Representation.GodementJacquet.TwoBlockAnalyticReversal
import Langlands.AllField.Representation.GodementJacquet.InverseTransposeProductAnalytics
import Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement
/-!
# Canonical analytic inputs for the reversed inverse-transpose block family

These adapters identify the actual reversed family in the published matrix
analytic predicate, and transport its admissibility and scalar central action.
They do not supply the noncompact analytic-induction argument.
-/

noncomputable section

universe uF uV

namespace Langlands.AllField.GeneralLinear
open Langlands.GeneralLinear
open Langlands.AllField.GeneralLinear

end Langlands.AllField.GeneralLinear

namespace Langlands.AllField.Classification
open Langlands.Classification
open Langlands.AllField.Classification

end Langlands.AllField.Classification

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff
open Langlands.AllField.GodementJacquet

open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

namespace Padic
open Langlands.GodementJacquet.Padic hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instMeasurableSpaceCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instValuativeRelCarrier instValuativeRelCarrier_1 iotaMatrixAnalyticAssertions_succBlocks_iff iotaMatrixRationalValues jpssI2 jpssI3 matrixAnalyticAssertions_reversedInverseTransposeBlocks matrixIntegral matrixIntegrand matrixRationalValues twoBlockReversalGLBorel twoBlockReversalGLMeasurable twoBlockReversalLocalField twoBlockReversalTopology twoBlockReversalValuation whittakerRationalValues
open Langlands.AllField.GodementJacquet.Padic
open Langlands.GodementJacquet hiding IotaMatrixAnalyticAssertions IotaMatrixConvergesOnRight IsIotaMatrixNormalizedGenerator IsMatrixNormalizedGenerator MatrixAnalyticAssertions MatrixConverges MatrixConvergesOnRight MatrixFourierPair NormalizedMatrixFunctionalEquationData inverseTransposeProductReversalEquiv iotaMatrixAnalyticAssertions_product_iff iotaMatrixRationalValues jpssI2 jpssI3 matrixIntegral matrixIntegrand matrixRationalValues whittakerRationalValues
open Langlands.AllField.GodementJacquet

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance twoBlockReversalGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear (n + 1) F) :=
  borel _
local instance twoBlockReversalGLBorel (n : ℕ) : BorelSpace (GeneralLinear (n + 1) F) := ⟨rfl⟩

/-- Each block's actual transformed analytic assertion is precisely the
ordinary assertion for the corresponding reversed pullback block. -/
theorem matrixAnalyticAssertions_reversedInverseTransposeBlocks
    {k : ℕ} (m : Fin k → ℕ) {V : Fin k → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (V i))
    (P : Fin k → Polynomial ℂ)
    (h : ∀ i, IotaMatrixAnalyticAssertions F (σ i) (P i)) :
    ∀ i : Fin k,
      MatrixAnalyticAssertions F (reversedInverseTransposeBlocks m σ i) (P i.rev) := by
  intro i
  exact (iotaMatrixAnalyticAssertions_iff_comp_inverseTranspose
    (⟨⟩ : LocalFieldData F).residueCardinality
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (generalLinearHaar F (m i.rev)) (P i.rev)).mp (h i.rev)

/-- With canonical topology and Haar measure, the transformed assertion for
upper normalized induction is the ordinary assertion for upper normalized
induction of the complete reversed inverse-transpose block family. This
includes the reindexing of the proposed polynomial factors. -/
theorem iotaMatrixAnalyticAssertions_succBlocks_iff
    {k t : ℕ} (m : Fin k → ℕ) (h : ∑ i, (m i + 1) = t + 1)
    {V : Fin k → Type uV} [hadd : ∀ i, AddCommGroup (V i)]
    [hmod : ∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F) (V i))
    (hσ : ∀ i, IsSmooth (σ i)) (P : Fin k → Polynomial ℂ) :
    letI : ∀ i : Fin k, AddCommGroup (V i.rev) := fun i => hadd i.rev
    letI : ∀ i : Fin k, Module ℂ (V i.rev) := fun i => hmod i.rev
    IotaMatrixAnalyticAssertions F
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced (RankinSelberg.succBlockShape m h) σ)
        (∏ i, P i) ↔
      MatrixAnalyticAssertions F
        ((⟨⟩ : LocalFieldData F).normalizedProductInduced
          (RankinSelberg.succBlockShape (fun i => m i.rev) (sum_reversedSuccBlocks m h))
          (V := fun i => V i.rev) (reversedInverseTransposeBlocks m σ))
        (∏ i : Fin k, P i.rev) := by
  let : ∀ i : Fin k, AddCommGroup (V i.rev) := fun i => hadd i.rev
  let : ∀ i : Fin k, Module ℂ (V i.rev) := fun i => hmod i.rev
  have hP : (∏ i : Fin k, P i.rev) = ∏ i, P i :=
    Equiv.prod_comp Fin.revPerm P
  rw [hP]
  exact iotaMatrixAnalyticAssertions_product_iff (⟨⟩ : LocalFieldData F)
    (RankinSelberg.succBlockShape m h) σ hσ
    (⟨⟩ : LocalFieldData F).residueCardinality
    (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (generalLinearHaar F t) (∏ i, P i)

end Padic
end Langlands.AllField.GodementJacquet
