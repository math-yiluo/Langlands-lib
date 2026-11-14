import Langlands.Representation.RankinSelberg.TwoBlockUniverseTransport
import Langlands.AllField.Representation.Induction.BlockEquivalence
import Langlands.AllField.Representation.RankinSelberg.TwoBlockMultiplicativityStatement
/-!
# Carrier-universe transport for two-block pair factors

Internal equivalence transport only. The common-universe hypotheses below
remain analytic obligations; this module proves neither factor existence nor
multiplicativity without those hypotheses.
-/

noncomputable section

namespace Langlands.AllField

universe uF uV uW uX uY

end Langlands.AllField

namespace Langlands.LocalFieldData
universe uF uV uW uX uY
open Langlands.LocalFieldData

variable {F : Type uF} [Field F]

/-- Lift every carrier of the dependent block family through the actual
normalized upper induction, keeping the entire ordered block shape fixed. -/
def normalizedProductInducedUniverseLiftEquiv
    (T : LocalFieldData F) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {V : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).Equiv
      (T.normalizedProductInduced B (fun i => universeLiftRepresentation.{uX} (σ i))) :=
  T.normalizedProductInducedEquiv B (fun i => universeLiftEquiv.{uX} (σ i))

end Langlands.LocalFieldData

namespace Langlands.AllField
universe uF uV uW uX uY

namespace RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement GammaMultiplicativityStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial LFactorMultiplicativityStatement QuotientHaarExistenceStatement TwoBlockGammaMultiplicativityStatement TwoBlockLFactorMultiplicativityStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricGammaFactor_universeLift_iff isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_universeLift_iff normalizedAbsoluteValue normalizedAbsoluteValue_apply twoBlockGammaMultiplicativity_of_commonUniverse twoBlockLFactorMultiplicativity_of_commonUniverse
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.HarmonicAnalysis
open Langlands.Whittaker hiding functionalsCongr
open Langlands.GeneralLinear

section WhittakerType


end WhittakerType

section PairFactors

variable {F : Type uF} [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]
  {ψ : UnitaryAdditiveCharacter F}
  {ν : letI := borel F
    AdditiveHaarMeasure F}
  {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)

/-- Symmetric gamma certificates are unchanged under independent carrier lifts. -/
theorem isPadicSymmetricGammaFactor_universeLift_iff {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν
        (universeLiftRepresentation.{uX} π) (universeLiftRepresentation.{uY} σ) G ↔
      IsPadicSymmetricGammaFactor F ψ ν π σ G :=
  (Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv
    (universeLiftEquiv.{uX} π) (universeLiftEquiv.{uY} σ)).symm

/-- Symmetric L-polynomial certificates are unchanged under independent lifts. -/
theorem isPadicSymmetricLPolynomial_universeLift_iff {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν
        (universeLiftRepresentation.{uX} π) (universeLiftRepresentation.{uY} σ) P ↔
      IsPadicSymmetricLPolynomial F ψ ν π σ P :=
  (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv
    (universeLiftEquiv.{uX} π) (universeLiftEquiv.{uY} σ)).symm

end PairFactors

/-- Conditional carrier transport from a common universe closed under
normalized induction. This does not discharge the common-universe hypothesis. -/
theorem twoBlockGammaMultiplicativity_of_commonUniverse
    (hCommon :
      TwoBlockGammaMultiplicativityStatement.{uF, max uF uV uW, max uF uV uW}) :
    TwoBlockGammaMultiplicativityStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν r t m h V hVAdd hVMod W hWAdd hWMod π σ hπ hσ
  have hπ' := hπ.of_equiv (universeLiftEquiv.{max uF uV uW} π)
  have hσ' := fun i => (hσ i).of_equiv (universeLiftEquiv.{max uF uV uW} (σ i))
  obtain ⟨G, hG, hInd⟩ := hCommon F ψ ν r t m h
    (universeLiftRepresentation.{max uF uV uW} π)
    (fun i => universeLiftRepresentation.{max uF uV uW} (σ i)) hπ' hσ'
  refine ⟨G, fun i => ?_, ?_⟩
  · exact (isPadicSymmetricGammaFactor_universeLift_iff π (σ i)).mp (hG i)
  · exact (Langlands.AllField.RankinSelberg.IsPadicSymmetricGammaFactor.congr_equiv
      (universeLiftEquiv.{max uF uV uW} π)
      ((⟨⟩ : LocalFieldData F).normalizedProductInducedUniverseLiftEquiv
        (succBlockShape m h) σ)).mpr hInd

/-- Conditional carrier transport retaining the original certified
L-polynomials and the unchanged equation `X^e * ∏ i, Pi i = Q * P`. -/
theorem twoBlockLFactorMultiplicativity_of_commonUniverse
    (hCommon :
      TwoBlockLFactorMultiplicativityStatement.{uF, max uF uV uW, max uF uV uW}) :
    TwoBlockLFactorMultiplicativityStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν r t m h V hVAdd hVMod W hWAdd hWMod π σ hπ hσ
  have hπ' := hπ.of_equiv (universeLiftEquiv.{max uF uV uW} π)
  have hσ' := fun i => (hσ i).of_equiv (universeLiftEquiv.{max uF uV uW} (σ i))
  obtain ⟨P, Pi, hInd, hPi, hDiv⟩ := hCommon F ψ ν r t m h
    (universeLiftRepresentation.{max uF uV uW} π)
    (fun i => universeLiftRepresentation.{max uF uV uW} (σ i)) hπ' hσ'
  refine ⟨P, Pi, ?_, (fun i => ?_), hDiv⟩
  · exact (Langlands.AllField.RankinSelberg.IsPadicSymmetricLPolynomial.congr_equiv
      (universeLiftEquiv.{max uF uV uW} π)
      ((⟨⟩ : LocalFieldData F).normalizedProductInducedUniverseLiftEquiv
        (succBlockShape m h) σ)).mpr hInd
  · exact (isPadicSymmetricLPolynomial_universeLift_iff π (σ i)).mp (hPi i)

end RankinSelberg
end Langlands.AllField
