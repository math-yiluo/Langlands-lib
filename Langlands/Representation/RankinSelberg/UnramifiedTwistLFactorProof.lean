import Langlands.Representation.RankinSelberg.UnramifiedTwistStatement
import Langlands.Representation.RankinSelberg.UnramifiedTwistIntegrals
import Langlands.Representation.RankinSelberg.SpectralRescaling

noncomputable section

namespace Langlands.RankinSelberg

open GeneralLinear Whittaker HarmonicAnalysis MeasureTheory Polynomial QuotientIntegration

universe uF uV uW

section PairTransport

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
variable (u : ℂ) (e : RationalFunctions ≃ RationalFunctions) (Q : ℂ[X] → ℂ[X])
variable (hshift : ∀ (f : ℂ → ℂ) (R : RationalFunctions),
  HasRationalContinuation q (fun s => f (s + u)) (e R) ↔ HasRationalContinuation q f R)
variable (hgen : ∀ S P, IsNormalizedGenerator S P → IsNormalizedGenerator (e '' S) (Q P))
variable (χ : Fˣ →* ℂˣ)
variable (hχ : ∀ x : Fˣ, (χ x : ℂ) = (abv (x : F) : ℂ) ^ u)

include hshift hgen hχ

/-- Generic rank-case assembly, with the algebraic rescaling laws explicit. -/
theorem isPairLPolynomial_unramified_of_transport {r n : ℕ}
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    (μ : Measure (LeftUnipotentQuotient n F)) (ν : AdditiveHaarMeasure F)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    {P : ℂ[X]} (hP : IsPairLPolynomial q ψ abv μ ν π σ P) :
    IsPairLPolynomial q ψ abv μ ν π (Langlands.twist (χ.comp determinant) σ) (Q P) ∧
      IsPairLPolynomial q ψ abv μ ν (Langlands.twist (χ.comp determinant) π) σ (Q P) := by
  by_cases hnr : n < r
  · rw [isPairLPolynomial_of_lt hnr] at hP ⊢
    rw [isPairLPolynomial_of_lt hnr]
    constructor
    · intro j k hr
      subst r
      change IsNormalizedGenerator
        (unequalRankZetaValues q ψ abv j k μ (rectangularMeasure ν j (n + 1))
          π (Langlands.twist (χ.comp determinant) σ)) (Q P)
      rw [unequalRankZetaValues_unramified_right ψ abv q u e hshift χ hχ]
      exact hgen _ P (hP j k rfl)
    · intro j k hr
      subst r
      change IsNormalizedGenerator
        (unequalRankZetaValues q ψ abv j k μ (rectangularMeasure ν j (n + 1))
          (Langlands.twist (χ.comp determinant) π) σ) (Q P)
      rw [unequalRankZetaValues_unramified_left ψ abv q u e hshift χ hχ]
      exact hgen _ P (hP j k rfl)
  · by_cases hrn : r = n
    · subst r
      rw [isPairLPolynomial_self] at hP ⊢
      rw [isPairLPolynomial_self]
      change IsNormalizedGenerator
          (equalRankZetaValues q ψ abv μ π (Langlands.twist (χ.comp determinant) σ)) (Q P) ∧
        IsNormalizedGenerator
          (equalRankZetaValues q ψ abv μ (Langlands.twist (χ.comp determinant) π) σ) (Q P)
      rw [equalRankZetaValues_unramified_right ψ abv q u e hshift χ hχ,
        equalRankZetaValues_unramified_left ψ abv q u e hshift χ hχ]
      exact ⟨hgen _ P hP, hgen _ P hP⟩
    · exact False.elim ((not_isPairLPolynomial_of_lt (by omega)) hP)

end PairTransport

section PadicTransport

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
variable (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
  AdditiveHaarMeasure F.Carrier)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (u : ℂ) (e : RationalFunctions ≃ RationalFunctions) (Q : ℂ[X] → ℂ[X])
variable (hshift : ∀ (f : ℂ → ℂ) (R : RationalFunctions),
  HasRationalContinuation F.canonicalTopologicalData.residueCardinality
      (fun s => f (s + u)) (e R) ↔
    HasRationalContinuation F.canonicalTopologicalData.residueCardinality f R)
variable (hgen : ∀ S P, IsNormalizedGenerator S P → IsNormalizedGenerator (e '' S) (Q P))
variable (χ : F.Carrierˣ →* ℂˣ)
variable (hχ : ∀ x : F.Carrierˣ,
  (χ x : ℂ) = (F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℂ) ^ u)

include hshift hgen hχ

/-- Transport preserves the supplied compatible measure's existence and works
for every compatible quotient measure in the p-adic relation. -/
theorem isPadicPairLPolynomial_unramified_of_transport {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
    {P : ℂ[X]} (hP : IsPadicPairLPolynomial F ψ ν π σ P) :
    IsPadicPairLPolynomial F ψ ν π (Langlands.twist (χ.comp determinant) σ) (Q P) ∧
      IsPadicPairLPolynomial F ψ ν (Langlands.twist (χ.comp determinant) π) σ (Q P) := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (n + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (n + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient n F.Carrier)
  constructor
  · refine ⟨hP.1, ?_⟩
    intro _ μ hμ
    exact (isPairLPolynomial_unramified_of_transport
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      u e Q hshift hgen χ hχ μ ν π σ (hP.2 μ hμ)).1
  · refine ⟨hP.1, ?_⟩
    intro _ μ hμ
    exact (isPairLPolynomial_unramified_of_transport
      F.canonicalTopologicalData.residueCardinality ψ
      (normalizedAbsoluteValue F.canonicalTopologicalData)
      u e Q hshift hgen χ hχ μ ν π σ (hP.2 μ hμ)).2

/-- Rank-order symmetry turns the ordered-pair result into both twist relations. -/
theorem isPadicSymmetricLPolynomial_unramified_of_transport {r n : ℕ}
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W)
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
  intro p _ F ψ ν r t V _ _ W _ _ π σ u χ hχ P hP
  obtain ⟨e, hshift, hgen⟩ := H F.canonicalTopologicalData.residueCardinality
    F.canonicalTopologicalData.residueCardinality_gt_one u
  exact isPadicSymmetricLPolynomial_unramified_of_transport F ψ ν.val u e
    (fun P => P.comp (C ((F.canonicalTopologicalData.residueCardinality : ℂ) ^ (-u)) * X))
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

end Langlands.RankinSelberg
