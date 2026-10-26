import Langlands.Representation.Category.UniverseLift
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.RankinSelberg.TwoBlockMultiplicativityStatement

/-!
# Carrier-universe transport for two-block pair factors

Internal equivalence transport only. The common-universe hypotheses below
remain analytic obligations; this module proves neither factor existence nor
multiplicativity without those hypotheses.
-/

noncomputable section

namespace Langlands

universe uF uV uW uX uY

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- Lift every carrier of the dependent block family through the actual
normalized upper induction, keeping the entire ordered block shape fixed. -/
def normalizedProductInducedUniverseLiftEquiv
    (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
    {V : Fin B.length → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    (σ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedProductInduced B σ).Equiv
      (T.normalizedProductInduced B (fun i => universeLiftRepresentation.{uX} (σ i))) :=
  T.normalizedProductInducedEquiv B (fun i => universeLiftEquiv.{uX} (σ i))

end PadicField.TopologicalData

namespace RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear Polynomial

section WhittakerType

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {θ : upperUnipotent (n + 1) F →* ℂˣ}
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- Lifting preserves the entire Whittaker-type predicate, including the
functional-space equivalence and finite generation over the group algebra. -/
theorem isOfWhittakerType_universeLift_iff :
    IsOfWhittakerType n θ (universeLiftRepresentation.{uX} π) ↔
      IsOfWhittakerType n θ π :=
  (isOfWhittakerType_iff_of_equiv (universeLiftEquiv.{uX} π)).symm

end WhittakerType

section PairFactors

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)

/-- Symmetric gamma certificates are unchanged under independent carrier lifts. -/
theorem isPadicSymmetricGammaFactor_universeLift_iff {G : RationalFunctions} :
    IsPadicSymmetricGammaFactor F ψ ν
        (universeLiftRepresentation.{uX} π) (universeLiftRepresentation.{uY} σ) G ↔
      IsPadicSymmetricGammaFactor F ψ ν π σ G :=
  (IsPadicSymmetricGammaFactor.congr_equiv
    (universeLiftEquiv.{uX} π) (universeLiftEquiv.{uY} σ)).symm

/-- Symmetric L-polynomial certificates are unchanged under independent lifts. -/
theorem isPadicSymmetricLPolynomial_universeLift_iff {P : ℂ[X]} :
    IsPadicSymmetricLPolynomial F ψ ν
        (universeLiftRepresentation.{uX} π) (universeLiftRepresentation.{uY} σ) P ↔
      IsPadicSymmetricLPolynomial F ψ ν π σ P :=
  (IsPadicSymmetricLPolynomial.congr_equiv
    (universeLiftEquiv.{uX} π) (universeLiftEquiv.{uY} σ)).symm

end PairFactors

/-- Conditional carrier transport from a common universe closed under
normalized induction. This does not discharge the common-universe hypothesis. -/
theorem twoBlockGammaMultiplicativity_of_commonUniverse
    (hCommon :
      TwoBlockGammaMultiplicativityStatement.{uF, max uF uV uW, max uF uV uW}) :
    TwoBlockGammaMultiplicativityStatement.{uF, uV, uW} := by
  intro p hp F ψ ν r t m h V hVAdd hVMod W hWAdd hWMod π σ hπ hσ
  let := F.canonicalTopologicalData.topology
  have hπ' := hπ.of_equiv (universeLiftEquiv.{max uF uV uW} π)
  have hσ' := fun i => (hσ i).of_equiv (universeLiftEquiv.{max uF uV uW} (σ i))
  obtain ⟨G, hG, hInd⟩ := hCommon p F ψ ν r t m h
    (universeLiftRepresentation.{max uF uV uW} π)
    (fun i => universeLiftRepresentation.{max uF uV uW} (σ i)) hπ' hσ'
  refine ⟨G, fun i => ?_, ?_⟩
  · exact (isPadicSymmetricGammaFactor_universeLift_iff π (σ i)).mp (hG i)
  · exact (IsPadicSymmetricGammaFactor.congr_equiv
      (universeLiftEquiv.{max uF uV uW} π)
      (F.canonicalTopologicalData.normalizedProductInducedUniverseLiftEquiv
        (succBlockShape m h) σ)).mpr hInd

/-- Conditional carrier transport retaining the original certified
L-polynomials and the unchanged equation `X^e * ∏ i, Pi i = Q * P`. -/
theorem twoBlockLFactorMultiplicativity_of_commonUniverse
    (hCommon :
      TwoBlockLFactorMultiplicativityStatement.{uF, max uF uV uW, max uF uV uW}) :
    TwoBlockLFactorMultiplicativityStatement.{uF, uV, uW} := by
  intro p hp F ψ ν r t m h V hVAdd hVMod W hWAdd hWMod π σ hπ hσ
  let := F.canonicalTopologicalData.topology
  have hπ' := hπ.of_equiv (universeLiftEquiv.{max uF uV uW} π)
  have hσ' := fun i => (hσ i).of_equiv (universeLiftEquiv.{max uF uV uW} (σ i))
  obtain ⟨P, Pi, hInd, hPi, hDiv⟩ := hCommon p F ψ ν r t m h
    (universeLiftRepresentation.{max uF uV uW} π)
    (fun i => universeLiftRepresentation.{max uF uV uW} (σ i)) hπ' hσ'
  refine ⟨P, Pi, ?_, (fun i => ?_), hDiv⟩
  · exact (IsPadicSymmetricLPolynomial.congr_equiv
      (universeLiftEquiv.{max uF uV uW} π)
      (F.canonicalTopologicalData.normalizedProductInducedUniverseLiftEquiv
        (succBlockShape m h) σ)).mpr hInd
  · exact (isPadicSymmetricLPolynomial_universeLift_iff π (σ i)).mp (hPi i)

end RankinSelberg
end Langlands
