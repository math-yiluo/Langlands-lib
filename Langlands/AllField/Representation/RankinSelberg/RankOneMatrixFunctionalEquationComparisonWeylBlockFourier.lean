import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonWeylBlockFourier
import Langlands.AllField.Representation.RankinSelberg.AnalyticBridge
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonUnipotentIota
import Langlands.AllField.Representation.RankinSelberg.UnequalRankFiniteExpansionProof
/-! Actual signed Weyl and rectangular block coordinates for the affine Fourier identity. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped BigOperators

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement normalizedAbsoluteValue normalizedAbsoluteValue_apply signedWeyl_affineBlock_fourier_duality unequalRankFiniteExpansion weylBlockBorelSpace weylBlockLocalField weylBlockMeasurableSpace weylBlockNBorelSpace weylBlockNLocallyCompact weylBlockNMeasurableSpace weylBlockNSecondCountable weylBlockSecondCountable weylBlockSigmaCompact weylBlockT2 weylBlockTopology weylBlockTotallyDisconnected weylBlockValuativeRel
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicRectangularFourierIntegral_leftRight padicRectangularHaarScaling padicRectangularLeftRight_measurePreserving padicScalarHaarScaling padicUnipotentHaar_iota_fourier_duality_right
open Langlands.AllField.HarmonicAnalysis
open Langlands.RankinSelberg.UnequalRankComplementaryConjugationProof

universe uK

variable {K : Type uK} [Field K]

section Kernels


end Kernels

section CanonicalPadic

variable (F : Type uK) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance weylBlockT2 : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance weylBlockSecondCountable : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance weylBlockSigmaCompact : SigmaCompactSpace F :=
  (⟨⟩ : LocalFieldData F).sigmaCompactSpace
local instance weylBlockMeasurableSpace : MeasurableSpace F := borel _
local instance weylBlockBorelSpace : BorelSpace F := ⟨rfl⟩
local instance weylBlockNMeasurableSpace (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F) := borel _
local instance weylBlockNBorelSpace (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
local instance weylBlockNLocallyCompact (n : ℕ) :
    LocallyCompactSpace (upperUnipotent (n + 1) F) :=
  (upperEntryCoordinates (n + 1) (K := F)).isClosedEmbedding.locallyCompactSpace
local instance weylBlockNSecondCountable (n : ℕ) :
    SecondCountableTopology (upperUnipotent (n + 1) F) :=
  (upperEntryCoordinates (n + 1) (K := F)).secondCountableTopology
local instance weylBlockTotallyDisconnected : TotallyDisconnectedSpace F := by
  let : NonarchimedeanRing F := by
    convert! ValuativeRel.nonarchimedeanRing F
    exact Valuation.toTopologicalSpace_eq _
  infer_instance

set_option maxHeartbeats 800000 in
/-- The actual affine Fourier equality in signed Weyl and rectangular block
coordinates. Both full product integrands are integrable for the same supplied
self-dual scalar Haar measure and the actual integral-normalized unipotent Haar. -/
theorem signedWeyl_affineBlock_fourier_duality
    (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F)
    (hsd : IsSelfDual ψ ν) (m : ℕ)
    (h : Langlands.GeneralLinear (m + 2) F)
    (hh : (⟨⟩ : LocalFieldData F).determinantNorm (m + 2) h = 1)
    (Φ : SchwartzBruhat (Matrix (Fin (m + 2)) (Fin (m + 2)) F)) :
    Integrable (signedWeylScalarFourierKernel ψ ν m h Φ)
      ((unipotentHaar F (m + 1)).prod ν.measure) ∧
    Integrable (affineBlockFourierKernel ψ m h Φ)
      ((unipotentHaar F (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1))) ∧
    (∫ z, signedWeylScalarFourierKernel ψ ν m h Φ z
      ∂(unipotentHaar F (m + 1)).prod ν.measure) =
    ∫ z, affineBlockFourierKernel ψ m h Φ z
      ∂(unipotentHaar F (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1)) := by
  obtain ⟨hl, hr, he⟩ := padicUnipotentHaar_iota_fourier_duality_right
    F (⟨⟩ : LocalFieldData F) (m + 1) ψ ν hsd
      (unipotentHaar F (m + 1)) h hh Φ
  let e := (MeasurableEquiv.refl (upperUnipotent (m + 2) F)).prodCongr
    (rankOneAffineParametersEquiv (K := F) m)
  have hp : MeasurePreserving e
      ((unipotentHaar F (m + 1)).prod
        (ν.measure.prod (rectangularMeasure ν m 1)))
      ((unipotentHaar F (m + 1)).prod (rowMeasure ν (m + 1))) :=
    (MeasurePreserving.id _).prod (rankOneAffineParameters_preserving ν m)
  have hri := hp.integrable_comp_of_integrable hr
  have hei := hp.integral_comp e.measurableEmbedding
    (fun z : upperUnipotent (m + 2) F × (Fin (m + 1) → F) =>
      inverseUnipotentFourierPhase ψ (m + 1) z.1 *
        Φ (z.1.val.val * firstColumnMatrix (m + 1) z.2 *
          (inverseTranspose (m + 2) F h).val))
  change Integrable
    (fun z : upperUnipotent (m + 2) F ×
        (F × Matrix (Fin m) (Fin 1) F) =>
      inverseUnipotentFourierPhase ψ (m + 1) z.1 *
        Φ (z.1.val.val * firstColumnMatrix (m + 1) (rankOneAffineParameters m z.2) *
          (inverseTranspose (m + 2) F h).val)) _ at hri
  change (∫ z : upperUnipotent (m + 2) F ×
      (F × Matrix (Fin m) (Fin 1) F),
    inverseUnipotentFourierPhase ψ (m + 1) z.1 *
      Φ (z.1.val.val * firstColumnMatrix (m + 1) (rankOneAffineParameters m z.2) *
        (inverseTranspose (m + 2) F h).val)
    ∂(unipotentHaar F (m + 1)).prod
      (ν.measure.prod (rectangularMeasure ν m 1))) = _ at hei
  have heq := he.trans hei.symm
  simpa +unfoldPartialApp only [signedWeylScalarFourierKernel, affineBlockFourierKernel,
    unipotentFourierSum_inverseCharacter,
    cyclicShiftMatrix_eq_signedWeyl (m + 1) (by omega), Matrix.mul_assoc]
    using And.intro hl (And.intro hri heq)

end CanonicalPadic

end Langlands.AllField.RankinSelberg
