import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.AllField.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.AllField.Representation.Whittaker.InducedFiniteTypeProof
import Langlands.AllField.Representation.Whittaker.InducedWhittakerTypeProof
/-! # Full Whittaker type of normalized upper block induction -/

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement NormalizedProductWhittakerTypeStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedProductWhittakerType
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis hiding padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker hiding CompactLocalizationStatement UnipotentOrbitStatement compactLocalization functionalsCongr inducedLocalization_of_prerequisites unipotentOrbit
open Langlands.AllField.Whittaker
open Langlands.GeneralLinear hiding upperUnipotentCompactContainment upperUnipotent_isLimitOfCompactSubgroups
open Langlands.AllField.GeneralLinear

universe uF uW

/-- Actual normalized upper block induction preserves all three clauses of full
Whittaker type for arbitrary full-type blocks. -/
theorem normalizedProductWhittakerType :
    NormalizedProductWhittakerTypeStatement.{uF, uW} := by
  intro F _ _ _ _ ψ t k m h W _ _ σ hσ
  let T := (⟨⟩ : LocalFieldData F)
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1)
  let B := succBlockShape m h
  let τ := T.blockHalfTwist B σ
  have hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i) := by
    intro i
    exact (isOfWhittakerType_twist_iff (standardCharacter ψ (m i))
      (T.blockHalfModulus B i) (σ i) (T.isOpen_ker_blockHalfModulus B i)
      (T.blockHalfModulus_upperUnipotent B i)).mpr (hσ i)
  have hadm : IsAdmissible ((⟨⟩ : LocalFieldData F).normalizedProductInduced B σ) :=
    Langlands.AllField.Parabolic.normalizedInductionAdmissibility F T B _ (B.blockTensor σ)
      (FiniteTensor.isAdmissible_external σ (fun i => (hσ i).1))
  have hfinite := Langlands.AllField.inducedFiniteType.{uF, uW} F t B W τ (fun i => (hτ i).1)
    (fun i => (hτ i).2.1)
  have hne : ψ.complex ≠ 1 := by
    intro he
    apply ψ.nontrivial
    ext x
    exact congrArg (fun χ : AddChar F ℂ => χ x) he
  have hraw := (Langlands.AllField.inducedWhittakerType.{uF, uW}
    F t B W τ ψ.complex ψ.continuous_complex hne
    ψ.norm_complex (fun i => (hτ i).1) (fun i => (hτ i).2.1)).mpr
    (fun i => (nonempty_standardFunctionalsEquiv_iff ψ (m i) (τ i)).mp (hτ i).2.2)
  have hline := (nonempty_standardFunctionalsEquiv_iff ψ t
    (Induction.smoothInduced (B.parabolic F)
      ((B.blockTensor τ).comp (B.leviProjection F)))).mpr hraw
  let e := T.normalizedProductHalfAbsorptionEquiv B σ
  refine ⟨hadm, (finite_asModule_iff_of_equiv e).mpr hfinite, ?_⟩
  obtain ⟨l⟩ := hline
  exact ⟨(Whittaker.functionalsCongr e).trans l⟩

end Langlands.AllField.RankinSelberg
