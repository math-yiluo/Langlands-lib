import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.RankinSelberg.PairFactors
import Langlands.LocalFactor.ResidueReflection

/-!
# From a matrix functional equation on a Whittaker model to the rank-one gamma factor

A conditional form of JPS 1979, Section 4.4 and Theorem 4.5 (printed pages
194–198), for the trivial rank-one test and every rank including rank one.
The normalized matrix functional equation is a premise on the actual coefficient
model of one nonzero standard functional. This module only defines the proposition.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV

/-- JPS 1979, Section 4.4 and Theorem 4.5 (printed pages 194–198), conditional
form for the trivial rank-one test. Let `σ` be a representation of `GL_(n+1)(F)`
of full Whittaker type for the standard character, possibly reducible, let `ℓ`
be a nonzero standard Whittaker functional, and let `ν` be a Haar measure
self-dual for `ψ`. If the right-translation representation on the coefficient
image of `ℓ` has normalized matrix functional-equation data `(P, PDual, c, a)`
for `ψ` and `ν`, then `c q^(-a s) P(q^(-s)) / PDual(q^(-(1-s)))` is the
symmetric JPSS gamma factor of `σ` against the trivial character of `GL_1`. -/
def RankOneMatrixFunctionalEquationComparisonStatement : Prop :=
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
    ∀ (P PDual : Polynomial ℂ) (c : ℂˣ) (a : ℤ),
      GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν
          (V := (glCoefficientModel ψ n σ ℓ).toSubmodule)
          (glModelRepresentation ψ n σ ℓ) P PDual c a →
        IsPadicSymmetricGammaFactor F ψ ν σ
          (rankOneCharacter (1 : F.Carrierˣ →* ℂˣ))
          (rationalGammaExpression (LocalFactor.residueReflection F) c a P PDual)

end Langlands.RankinSelberg
