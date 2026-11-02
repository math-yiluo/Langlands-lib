import Langlands.Global.Factors.SeparationStatement
import Langlands.Global.Factors.GLPoleRegionStatement
import Langlands.Correspondence.FullGammaCompatibility
import Langlands.Correspondence.AutomorphicPairFactors

/-!
# Conditional separation on the existing certified pair-factor interfaces
-/

noncomputable section

namespace Langlands.Global.FactorSeparation

universe uF uP uA uE

open Correspondence LocalFactor LocalFactor.CommonClosure Weil.Local Polynomial

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- No reflected cancellation for every supplied original/dual class
L-polynomial at a self-dual measure. This is an analytic input, not a
consequence of equality of gamma factors. -/
def CertifiedAutomorphicPoleRegions (ψ : NontrivialAdditiveCharacter F)
    {r t : ℕ} (π : AutomorphicClass.{uF, uA} F r.succPNat)
    (π' : AutomorphicClass.{uF, uA} F t.succPNat) : Prop :=
  ∀ (ν : LocalAdditiveHaarMeasure F), IsSelfDualMeasure F ψ ν →
    ∀ (πd : AutomorphicClass.{uF, uA} F r.succPNat)
      (πd' : AutomorphicClass.{uF, uA} F t.succPNat) (P Pd : ℂ[X]),
      IsSmoothDual F π πd → IsSmoothDual F π' πd' →
      IsAutomorphicPairLPolynomial F ψ ν π π' P →
      IsAutomorphicPairLPolynomial F ψ ν πd πd' Pd →
      GLPoleRegion.HasNoReflectedCommonZero
        F.canonicalTopologicalData.residueCardinality P Pd

/-- The separated factors at all self-dual measures, for the exact supplied
system and actual pair classes. Both reciprocal Euler polynomials and the
coefficient/exponent of epsilon are identified. -/
def CertifiedSeparatedPairFactors
    (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uE} F)
    (hε : NonabelianSystem.IsSystem F eC ε) (ψ : NontrivialAdditiveCharacter F)
    (X Y : LocalPairClass.{uF, uP} F)
    (A : LocalWeilDeligneRepresentation.{uF, uP} F)
    {r t : ℕ} (π : AutomorphicClass.{uF, uA} F r.succPNat)
    (π' : AutomorphicClass.{uF, uA} F t.succPNat) : Prop :=
  (∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν) ∧
  ∀ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν →
    ∃ (πd : AutomorphicClass.{uF, uA} F r.succPNat)
      (πd' : AutomorphicClass.{uF, uA} F t.succPNat)
      (P Pd : ℂ[X]) (e : ℂˣ × ℤ),
      IsSmoothDual F π πd ∧ IsSmoothDual F π' πd' ∧
      IsAutomorphicPairLPolynomial F ψ ν π π' P ∧
      IsAutomorphicPairLPolynomial F ψ ν πd πd' Pd ∧
      IsAutomorphicPairEpsilonFactor F ψ ν π π' e ∧
      IsArithmeticPairEpsilonFactor F eC ε hε ψ X Y e.1 e.2 ∧
      P = WeilDeligne.eulerPolynomial A (localInertia F) (localGeometricFrobenius F) ∧
      Pd = WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A)
        (localInertia F) (localGeometricFrobenius F) ∧
      arithmeticPairLFactor F X Y = (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹ ∧
      WeilDeligne.rationalLFactor (WeilDeligneRepresentation.dual A)
        (localInertia F) (localGeometricFrobenius F) =
          (algebraMap ℂ[X] (RatFunc ℂ) Pd)⁻¹

/-- The actual-factor adapter to the four-polynomial separation theorem.
The tensor representative, common gamma factors, no-cancellation conditions,
and measure existence are all explicit. -/
def CertifiedFactorSeparationStatement : Prop :=
  ∀ (eC : ReciprocityFamily F) (ε : NonabelianSystem.Assignment.{uF, uE} F)
    (hε : NonabelianSystem.IsSystem F eC ε) (ψ : NontrivialAdditiveCharacter F)
    (X Y : LocalPairClass.{uF, uP} F)
    (A : LocalWeilDeligneRepresentation.{uF, uP} F),
    WeilDeligneRepresentation.classOf A = WeilDeligneRepresentation.tensorClass X Y →
    ∀ (r t : ℕ) (π : AutomorphicClass.{uF, uA} F r.succPNat)
      (π' : AutomorphicClass.{uF, uA} F t.succPNat),
      GLPoleRegion.HasNoReflectedCommonZero
        F.canonicalTopologicalData.residueCardinality
        (WeilDeligne.eulerPolynomial A (localInertia F) (localGeometricFrobenius F))
        (WeilDeligne.eulerPolynomial (WeilDeligneRepresentation.dual A)
          (localInertia F) (localGeometricFrobenius F)) →
      CertifiedAutomorphicPoleRegions F ψ π π' →
      ((∃ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν) ∧
        ∀ ν : LocalAdditiveHaarMeasure F, IsSelfDualMeasure F ψ ν →
          ∃ G : RatFunc ℂ,
            IsAutomorphicPairGammaFactor F ψ ν π π' G ∧
            IsArithmeticPairGammaFactor F eC ε hε ψ X Y G) →
      CertifiedSeparatedPairFactors F eC ε hε ψ X Y A π π'

end Langlands.Global.FactorSeparation
