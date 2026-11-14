import Langlands.Representation.RankinSelberg.UnramifiedTwistLFactorProof
import Langlands.AllField.Representation.RankinSelberg.UnramifiedTwistStatement
noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement IsPadicPairEpsilonFactor IsPadicPairGammaFactor IsPadicPairLPolynomial IsPadicSymmetricEpsilonFactor IsPadicSymmetricGammaFactor IsPadicSymmetricLPolynomial QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement UnramifiedTwistLFactorStatement isPadicPairLPolynomial_unramified_of_transport isPadicSymmetricEpsilonFactor_of_le isPadicSymmetricGammaFactor_of_le isPadicSymmetricGammaFactor_of_lt isPadicSymmetricLPolynomial_of_le isPadicSymmetricLPolynomial_of_lt isPadicSymmetricLPolynomial_unramified_of_transport normalizedAbsoluteValue normalizedAbsoluteValue_apply unramifiedTwistLFactor unramifiedTwistLFactor_of_transport
open Langlands.AllField.RankinSelberg

open _root_.MeasureTheory _root_.Polynomial
open Langlands.GeneralLinear
open Langlands.Whittaker
open Langlands.HarmonicAnalysis
open Langlands.QuotientIntegration

universe uF uV uW

section PairTransport



end PairTransport

section PadicTransport

variable (F : Type uF) [Field F]
variable [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (ψ : UnitaryAdditiveCharacter F)
variable (ν : letI := borel F
  AdditiveHaarMeasure F)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (u : ℂ) (e : RationalFunctions ≃ RationalFunctions) (Q : ℂ[X] → ℂ[X])
variable (hshift : ∀ (f : ℂ → ℂ) (R : RationalFunctions),
  HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality
      (fun s => f (s + u)) (e R) ↔
    HasRationalContinuation (⟨⟩ : LocalFieldData F).residueCardinality f R)
variable (hgen : ∀ S P, IsNormalizedGenerator S P → IsNormalizedGenerator (e '' S) (Q P))
variable (χ : Fˣ →* ℂˣ)
variable (hχ : ∀ x : Fˣ,
  (χ x : ℂ) = ((⟨⟩ : LocalFieldData F).normalizedAbs (x : F) : ℂ) ^ u)

include hshift hgen hχ

/-- Transport preserves the supplied compatible measure's existence and works
for every compatible quotient measure in the p-adic relation. -/
theorem isPadicPairLPolynomial_unramified_of_transport {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν π σ P) :
    IsPadicPairLPolynomial F ψ ν π (Langlands.twist (χ.comp determinant) σ) (Q P) ∧
      IsPadicPairLPolynomial F ψ ν (Langlands.twist (χ.comp determinant) π) σ (Q P) := by
  let := borel F
  let : BorelSpace F := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F)
  let : BorelSpace (upperUnipotent (n + 1) F) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F)
  constructor
  · refine ⟨hP.1, ?_⟩
    intro _ μ hμ
    exact (isPairLPolynomial_unramified_of_transport
      (⟨⟩ : LocalFieldData F).residueCardinality ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      u e Q hshift hgen χ hχ μ ν π σ (hP.2 μ hμ)).1
  · refine ⟨hP.1, ?_⟩
    intro _ μ hμ
    exact (isPairLPolynomial_unramified_of_transport
      (⟨⟩ : LocalFieldData F).residueCardinality ψ
      (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
      u e Q hshift hgen χ hχ μ ν π σ (hP.2 μ hμ)).2

/-- Rank-order symmetry turns the ordered-pair result into both twist relations. -/
theorem isPadicSymmetricLPolynomial_unramified_of_transport {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {P : ℂ[X]} (hP : IsPadicSymmetricLPolynomial F ψ ν π σ P) :
    IsPadicSymmetricLPolynomial F ψ ν π (Langlands.twist (χ.comp determinant) σ) (Q P) ∧
      IsPadicSymmetricLPolynomial F ψ ν (Langlands.twist (χ.comp determinant) π) σ (Q P) := by
  unfold IsPadicSymmetricLPolynomial at hP ⊢
  split_ifs at hP ⊢ with hnr
  · exact isPadicPairLPolynomial_unramified_of_transport F ψ ν u e Q hshift hgen χ hχ π σ hP
  · exact (isPadicPairLPolynomial_unramified_of_transport F ψ ν u e Q hshift hgen χ hχ σ π hP).symm

end PadicTransport

/-- Assemble the target from continuation and normalized-generator transport. -/
theorem unramifiedTwistLFactor_of_transport
    (H : ∀ (q : ℕ), 1 < q → ∀ (u : ℂ),
      ∃ (e : RationalFunctions ≃ RationalFunctions),
        (∀ (f : ℂ → ℂ) (R : RationalFunctions),
          HasRationalContinuation q (fun s => f (s + u)) (e R) ↔
            HasRationalContinuation q f R) ∧
        ∀ S P, IsNormalizedGenerator S P →
          IsNormalizedGenerator (e '' S) (P.comp (C ((q : ℂ) ^ (-u)) * X))) :
    UnramifiedTwistLFactorStatement.{uF, uV, uW} := by
  intro F _ _ _ _ ψ ν r t V _ _ W _ _ π σ u χ hχ P hP
  obtain ⟨e, hshift, hgen⟩ := H (⟨⟩ : LocalFieldData F).residueCardinality
    (⟨⟩ : LocalFieldData F).residueCardinality_gt_one u
  exact isPadicSymmetricLPolynomial_unramified_of_transport F ψ ν.val u e
    (fun P => P.comp (C (((⟨⟩ : LocalFieldData F).residueCardinality : ℂ) ^ (-u)) * X))
    hshift hgen χ hχ π σ hP

/-- Twisting either member by the supplied unramified character transports the
certified L-polynomial by `X ↦ q^(-u) * X`. -/
theorem unramifiedTwistLFactor : UnramifiedTwistLFactorStatement.{uF, uV, uW} := by
  apply unramifiedTwistLFactor_of_transport
  intro q hq u
  refine ⟨(rationalRescale (spectralShiftUnit q hq u)).toEquiv, ?_, ?_⟩
  · intro f R
    exact hasRationalContinuation_shift_iff hq f R u
  · intro S P hP
    simpa only [AlgEquiv.toEquiv_eq_coe, AlgEquiv.coe_toEquiv,
      coe_spectralShiftUnit, spectralPoint] using
      hP.rescale (spectralShiftUnit q hq u)

end Langlands.AllField.RankinSelberg
