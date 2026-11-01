import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonStatement

/-!
# Rank-one comparison from an ambient matrix functional equation

This internal conditional statement allows the actual coefficient model to have
its bi-smooth coefficients contained in those of a separate representation.
Normalized generators remain assertions about that ambient representation.
No comparison proof or analytic data existence is supplied here.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV uW

/-- Ambient form of the matrix-to-rank-one comparison. Full normalized matrix
data are assumed on `ρ`, and only actual coefficient inclusion is required for
the model of `σ`. The conclusion is the complete symmetric gamma certificate
for the original `σ` and the trivial rank-one test, including `n = 0`.
There is no claim that `P` or `PDual` generates constituent matrix values. -/
def RankOneAmbientMatrixFunctionalEquationComparisonStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI : MeasurableSpace F.Carrier := borel F.Carrier
    haveI : BorelSpace F.Carrier := ⟨rfl⟩
    haveI : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
    haveI : TotallyDisconnectedSpace F.Carrier := by
      let : NonarchimedeanRing F.Carrier := by
        convert! ValuativeRel.nonarchimedeanRing F.Carrier
        exact Valuation.toTopologicalSpace_eq _
      infer_instance
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier),
      IsSelfDual ψ ν →
    ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V),
      IsOfWhittakerType n (standardCharacter ψ n) σ →
    ∀ ℓ : glFunctionals ψ n σ, ℓ.val ≠ 0 →
    ∀ (W : Type uW) [AddCommGroup W] [Module ℂ W]
      (ρ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      GodementJacquet.biSmoothMatrixCoefficients
          (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
          (glModelRepresentation ψ n σ ℓ) ≤
        GodementJacquet.biSmoothMatrixCoefficients ρ →
    ∀ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
      GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
          ρ P PDual c a →
        IsPadicSymmetricGammaFactor F ψ ν σ
          (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
          (rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual)

end Langlands.RankinSelberg
