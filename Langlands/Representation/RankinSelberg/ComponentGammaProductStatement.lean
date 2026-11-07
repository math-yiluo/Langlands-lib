import Langlands.Representation.RankinSelberg.TemperedLFactorGamma
import Langlands.Representation.RankinSelberg.ComponentFactorComparisonStatement

/-! The reflected gamma ratio for actual components of two block inductions. -/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial TemperedLFactorGamma

universe uF uV uW uV₂ uW₂

/-- Supplied L-polynomials of full-Whittaker-type actual components and of all
block pairs satisfy the reflected ratio dictated by gamma multiplicativity. -/
def ComponentGammaProductStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t k l : ℕ) (m : Fin k → ℕ) (n : Fin l → ℕ)
    (hm : ∑ i, (m i + 1) = r + 1) (hn : ∑ j, (n j + 1) = t + 1)
    {V : Fin k → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
    {W : Fin l → Type uW} [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)]
    {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
    {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
    (ξ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))
    (η : ∀ j, Representation ℂ (Langlands.GeneralLinear (n j + 1) F.Carrier) (W j))
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V₂)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W₂),
    (∀ i, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (ξ i)) →
    (∀ j, letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType (n j) (standardCharacter ψ (n j)) (η j)) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType r (standardCharacter ψ r) π) →
    (letI := F.canonicalTopologicalData.topology;
      IsOfWhittakerType t (standardCharacter ψ t) σ) →
    IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape m hm) ξ) π →
    IsIrreducibleComponent
      (F.canonicalNormalizedProductInduced (succBlockShape n hn) η) σ →
    ∀ (P PD : ℂ[X]) (Q QD : Fin k → Fin l → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π σ P →
      (∀ i j, IsPadicSymmetricLPolynomial F ψ ν.val (ξ i) (η j) (Q i j)) →
      (letI := F.canonicalTopologicalData.topology;
        letI := F.canonicalTopologicalData.valuativeRel;
        letI := F.canonicalTopologicalData.localField;
        IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
          (inverseTransposePullback π) (inverseTransposePullback σ) PD) →
      (∀ i j, letI := F.canonicalTopologicalData.topology;
        letI := F.canonicalTopologicalData.valuativeRel;
        letI := F.canonicalTopologicalData.localField;
        IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
          (inverseTransposePullback (ξ i)) (inverseTransposePullback (η j)) (QD i j)) →
      Nonempty (ReflectedRatioData (LocalFactor.residueReflection F)
        P PD (∏ i, ∏ j, Q i j) (∏ i, ∏ j, QD i j))

end Langlands.RankinSelberg
