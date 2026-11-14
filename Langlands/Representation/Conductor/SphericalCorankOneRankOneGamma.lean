import Langlands.Representation.RankinSelberg.UnequalRankEpsilonConvergenceBridge
import Langlands.Representation.RankinSelberg.HighlyRamified.EssentialInput
import Langlands.Representation.RankinSelberg.RankOneWhittakerTypeProof
import Langlands.Representation.RankinSelberg.WhittakerGammaAdapters

/-!
# The gamma factor of `π × 1` from its epsilon factor and standard L-polynomials

Over an arbitrary nonarchimedean local field, let `π` be a representation of
`GL_(N+2)(F)` of Whittaker type whose inverse-transpose pullback is also of Whittaker
type. If `c q^(-ms)` is the epsilon factor of `π` against the trivial character `1` of
`GL_1`, and `P`, `P̃` are the standard L-polynomials of `π` and of its inverse-transpose
pullback, then `rationalGammaExpression δ c m P P̃` is the gamma factor of `π × 1`, provided
that the block-zero integrals of `π × 1` and of the dual pair converge on right
half-planes. This is the identity `γ = ε · L(1 - s, π̃) / L(s, π)` of
Jacquet, Piatetski-Shapiro and Shalika 1983, Theorem (2.7)(iii), printed page 390,
specialized to the pair `π × 1`.
-/

noncomputable section

namespace Langlands.Conductor.SphericalCorankOne

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration Polynomial
open Langlands.RankinSelberg LocalFactor

universe uF uV

section Character

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- The trivial character of `GL_1`, pulled back along inverse transpose, is itself. -/
theorem inverseTransposePullback_rankOneCharacter_one :
    inverseTransposePullback (rankOneCharacter (1 : Fˣ →* ℂˣ)) =
      rankOneCharacter (1 : Fˣ →* ℂˣ) := by
  ext g
  simp [inverseTransposePullback, characterRepresentation, twist]

omit [IsTopologicalRing F] in
/-- The trivial character of `GL_1` is of Whittaker type for every additive character. -/
theorem isOfWhittakerType_rankOneCharacter_one (ψ : UnitaryAdditiveCharacter F) :
    IsOfWhittakerType 0 (standardCharacter ψ 0) (rankOneCharacter (1 : Fˣ →* ℂˣ)) := by
  apply scalar_isOfWhittakerType_rankOne
  intro v
  refine ⟨⊤, ?_⟩
  intro g
  simp [characterRepresentation, twist]

end Character

section Gamma

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)] [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)] [BorelSpace (LeftUnipotentQuotient 0 F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V] {N : ℕ}
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (N + 1 + 1) F) V}

/-- JPSS 1983, Theorem (2.7)(iii), for `π × 1`: the epsilon factor `(c, m)` of `π`
against the trivial character of `GL_1` and the standard L-polynomials `P` of `π` and
`P̃` of its inverse-transpose pullback give the gamma factor
`rationalGammaExpression δ c m P P̃`, provided the block-zero integrals of `π × 1` and of
the dual pair converge on right half-planes for every pair of nonzero functionals. -/
theorem isPairGammaFactor_rankOne_of_convergence (hq : 1 < q)
    {δ : ℂˣ} (hδ : (δ : ℂ) = (q : ℂ)⁻¹) {c : ℂˣ} {m : ℤ} {P Pdual : ℂ[X]}
    (hπ : IsOfWhittakerType (N + 1) (standardCharacter ψ (N + 1)) π)
    (hπd : IsOfWhittakerType (N + 1) (standardCharacter (ψ.scale (-1)) (N + 1))
      (inverseTransposePullback π))
    (hC : ∀ (ℓ : glFunctionals ψ (N + 1) π)
      (ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ))),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      UnequalRankConvergenceAt 0 N (by omega) ψ abv (rankOneQuotientHaar F)
        (rectangularMeasure ν 0 (0 + 1)) π (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ ℓ')
    (hCd : ∀ (ℓ : glFunctionals ψ (N + 1) π)
      (ℓ' : glInverseFunctionals ψ 0 (rankOneCharacter (1 : Fˣ →* ℂˣ))),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      UnequalRankConvergenceAt 0 N (by omega) (ψ.scale (-1)) abv (rankOneQuotientHaar F)
        (rectangularMeasure ν 0 (0 + 1)) (inverseTransposePullback π)
        (inverseTransposePullback (rankOneCharacter (1 : Fˣ →* ℂˣ)))
        (firstDualFunctional ψ π ℓ)
        (secondDualFunctional ψ (rankOneCharacter (1 : Fˣ →* ℂˣ)) ℓ'))
    (hε : IsPairEpsilonFactor q ψ abv ν π (rankOneCharacter (1 : Fˣ →* ℂˣ)) (c, m))
    (hP : IsCharacterLPolynomial q ψ abv (rankOneQuotientHaar F) 1 π P)
    (hPd : IsCharacterLPolynomial q (ψ.scale (-1)) abv (rankOneQuotientHaar F) 1
      (inverseTransposePullback π) Pdual) :
    IsPairGammaFactor q ψ abv ν π (rankOneCharacter (1 : Fˣ →* ℂˣ))
      (rationalGammaExpression δ c m P Pdual) := by
  have hnr : 0 < N + 1 := Nat.succ_pos N
  rw [isPairEpsilonFactor_of_lt hnr] at hε
  rw [isPairGammaFactor_of_lt hnr]
  obtain ⟨hμex, hℓex, hℓ'ex, hall⟩ := hε
  refine ⟨hμex, hℓex, hℓ'ex, ?_⟩
  intro hinv μ hμ ℓ ℓ' hℓ hℓ'
  have hmeas : μ = rankOneQuotientHaar F :=
    (unipotentQuotientHaar_unique F 0 μ hμ).trans
      (unipotentQuotientHaar_unique F 0 _ (rankOneQuotientHaar_isCompatible F)).symm
  subst hmeas
  have h1 : IsOfWhittakerType 0 (inverseStandardCharacter ψ 0)
      (rankOneCharacter (1 : Fˣ →* ℂˣ)) :=
    (isOfWhittakerType_standard_iff_inverse ψ _).mp (isOfWhittakerType_rankOneCharacter_one ψ)
  have h1d : IsOfWhittakerType 0 (inverseStandardCharacter (ψ.scale (-1)) 0)
      (inverseTransposePullback (rankOneCharacter (1 : Fˣ →* ℂˣ))) := by
    rw [inverseTransposePullback_rankOneCharacter_one]
    exact (isOfWhittakerType_standard_iff_inverse _ _).mp
      (isOfWhittakerType_rankOneCharacter_one _)
  obtain ⟨ζ, P₀, Pd₀, hζ, hgen⟩ := @hall hinv _ hμ ℓ ℓ' hℓ hℓ'
  have hr0 : N + 1 = 0 + (0 + N + 1) := by omega
  have hPP : P₀ = P := by
    have hz : IsNormalizedGenerator
        (unequalRankZetaValuesAt 0 N hr0 q ψ abv (rankOneQuotientHaar F)
          (rectangularMeasure ν 0 (0 + 1)) π (rankOneCharacter (1 : Fˣ →* ℂˣ))) P := by
      rw [← HighlyRamified.characterZetaValues_succ_eq q ψ abv (rankOneQuotientHaar F) ν π]
      exact hP
    exact (hgen 0 N hr0).1.unique
      ((UnequalRankConvergenceAt.isNormalizedGenerator_iff 0 N hr0 (hC ℓ ℓ' hℓ hℓ')
        hπ h1 hℓ hℓ' P).mp hz)
  have hPdd : Pd₀ = Pdual := by
    have hrN : N + 1 = 0 + (N + 0 + 1) := by omega
    have h0 := (hgen N 0 hrN).2.1
    rw [dualUnequalRankRationalValuesAt_eq] at h0
    have hz : IsNormalizedGenerator
        (unequalRankZetaValuesAt 0 N hr0 q (ψ.scale (-1)) abv (rankOneQuotientHaar F)
          (rectangularMeasure ν 0 (0 + 1)) (inverseTransposePullback π)
          (inverseTransposePullback (rankOneCharacter (1 : Fˣ →* ℂˣ)))) Pdual := by
      rw [inverseTransposePullback_rankOneCharacter_one,
        ← HighlyRamified.characterZetaValues_succ_eq q (ψ.scale (-1)) abv
          (rankOneQuotientHaar F) ν (inverseTransposePullback π)]
      exact hPd
    exact h0.unique
      ((UnequalRankConvergenceAt.isNormalizedGenerator_iff 0 N hr0 (hCd ℓ ℓ' hℓ hℓ')
        hπd h1d (firstDualFunctional_ne_zero ψ π hℓ)
        (secondDualFunctional_ne_zero ψ _ hℓ') Pdual).mp hz)
  subst hPP
  subst hPdd
  exact UnequalRankEpsilonEquation.gammaEquation hq hδ
    (fun j k hr => (hgen j k hr).1) (fun j k hr => (hgen j k hr).2.1)
    ⟨ζ, P₀, Pd₀, hζ, hgen⟩

end Gamma

end Langlands.Conductor.SphericalCorankOne
