import Langlands.Representation.RankinSelberg.GammaFromWhittakerType
import Langlands.LocalFactor.Abelian.Padic
import Langlands.LocalFactor.ResidueReflection

/-!
# Canonical symmetric gamma expression from certified pair factors

A conditional statement using the published construction input and the intrinsic
epsilon and L-polynomial certificates. No analytic input is discharged here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear Polynomial

universe uF uV uW

/-- Conditional characterization of every symmetric gamma certificate by the
canonical rational epsilon-times-L-ratio expression, in either rank order. -/
def SymmetricGammaExpressionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    PadicSymmetricGammaConstructionInput F ψ ν.val π σ →
    ∀ (e : ℂˣ × ℤ) (P Pdual : ℂ[X]),
      IsPadicSymmetricEpsilonFactor F ψ ν.val π σ e →
      IsPadicSymmetricLPolynomial F ψ ν.val π σ P →
      IsPadicSymmetricLPolynomial F (ψ.scale (-1)) ν.val
        (inverseTransposePullback π) (inverseTransposePullback σ) Pdual →
      ∀ G : RationalFunctions,
        IsPadicSymmetricGammaFactor F ψ ν.val π σ G ↔
          G = rationalGammaExpression (LocalFactor.residueReflection F) e.1 e.2 P Pdual

end Langlands.RankinSelberg
