import Langlands.Representation.RankinSelberg.RankOneGammaTwistEquations
import Langlands.Representation.RankinSelberg.PadicPairFactors

/-! Rank-one determinant twists of the full JPSS epsilon certificate. -/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

namespace RankOneEpsilonTwist

section Equations

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient 0 F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
  (ℓ : glFunctionals ψ 0 π) (ellC : ℂ →ₗ[ℂ] ℂ)

open RankOneGammaTwist

omit [MeasurableSpace F] in
/-- The dual rational-value families agree for the same row tests. -/
theorem dual_values (q : ℕ) :
    dualEqualRankRationalValues q ψ abv μ (Langlands.twist (χ.comp determinant) π)
      (rankOneCharacter 1) (candidateFunctional ψ χ π ℓ) (testFunctional ψ 1 ellC) =
    dualEqualRankRationalValues q ψ abv μ π (rankOneCharacter χ) ℓ
      (testFunctional ψ χ ellC) := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, Φ, by
      rwa [equal_dual ψ χ abv μ ellC z π ℓ v Φ] at hR⟩
  · rintro ⟨f, f', Φ, hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, Φ, by
      rwa [← equal_dual ψ χ abv μ ellC z π ℓ v Φ] at hR⟩

/-- The same coefficient and exponent satisfy the fixed-functional equation
after moving the character between the two rank-one representations. -/
theorem equation (ν : AdditiveHaarMeasure F) (q : ℕ) (c : ℂˣ) (m : ℤ) :
    EqualRankEpsilonEquation q ψ abv μ ν (Langlands.twist (χ.comp determinant) π)
      (rankOneCharacter 1) (candidateFunctional ψ χ π ℓ) (testFunctional ψ 1 ellC) c m ↔
    EqualRankEpsilonEquation q ψ abv μ ν π (rankOneCharacter χ) ℓ
      (testFunctional ψ χ ellC) c m := by
  constructor
  · rintro ⟨ζ, P, Pd, -, hP, hPd, hFE⟩
    refine ⟨χ (-1), P, Pd, test_minusOne ψ χ ellC, ?_, ?_, ?_⟩
    · rwa [equal_values ψ χ abv μ π ℓ ellC q] at hP
    · rwa [dual_values ψ χ abv μ π ℓ ellC q] at hPd
    · intro f f' Φ
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨Φhat, R, Rd, hFourier, hR, hRd, heq⟩ :=
        hFE (modelMap _ _ v) (modelMap _ _ z) Φ
      refine ⟨Φhat, R, Rd, hFourier, ?_, ?_, ?_⟩
      · rwa [equal_forward ψ χ abv μ ellC z π ℓ v Φ] at hR
      · rwa [equal_dual ψ χ abv μ ellC z π ℓ v Φhat] at hRd
      · simpa only [NormalizedFunctionalEquation, pow_zero] using heq
  · rintro ⟨ζ, P, Pd, -, hP, hPd, hFE⟩
    refine ⟨1, P, Pd, (by simpa only [MonoidHom.one_apply] using test_minusOne ψ 1 ellC),
      ?_, ?_, ?_⟩
    · rwa [← equal_values ψ χ abv μ π ℓ ellC q] at hP
    · rwa [← dual_values ψ χ abv μ π ℓ ellC q] at hPd
    · intro f f' Φ
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨Φhat, R, Rd, hFourier, hR, hRd, heq⟩ :=
        hFE (modelMap _ _ v) (modelMap _ _ z) Φ
      refine ⟨Φhat, R, Rd, hFourier, ?_, ?_, ?_⟩
      · rwa [← equal_forward ψ χ abv μ ellC z π ℓ v Φ] at hR
      · rwa [← equal_dual ψ χ abv μ ellC z π ℓ v Φhat] at hRd
      · simpa only [NormalizedFunctionalEquation, pow_zero] using heq

end Equations

section Relations

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ) (abv : AbsoluteValue F ℝ)
  (ν : AdditiveHaarMeasure F)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)

open RankOneGammaTwist

/-- Transport of the complete epsilon certificate, including the existence
clauses and every compatible quotient measure and nonzero functional pair. -/
theorem factor (q : ℕ) (e : ℂˣ × ℤ) :
    IsEqualRankEpsilonFactor q ψ abv ν (Langlands.twist (χ.comp determinant) π)
      (rankOneCharacter 1) e ↔
    IsEqualRankEpsilonFactor q ψ abv ν π (rankOneCharacter χ) e := by
  constructor
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    let L := untwistFunctional _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) π ℓ
    refine ⟨hμ, ⟨L, hℓ⟩, ⟨testFunctional ψ χ ℓ'.val, hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    exact (equation ψ χ abv μ π L₀ L₀'.val ν q e.1 e.2).mp
      (@hall hinv μ hμc (candidateFunctional ψ χ π L₀)
        (testFunctional ψ 1 L₀'.val) hL₀ hL₀')
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    refine ⟨hμ, ⟨candidateFunctional ψ χ π ℓ, hℓ⟩,
      ⟨testFunctional ψ 1 ℓ'.val, hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    let L := untwistFunctional _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) π L₀
    exact (equation ψ χ abv μ π L L₀'.val ν q e.1 e.2).mpr
      (@hall hinv μ hμc L (testFunctional ψ χ L₀'.val) hL₀ hL₀')

end Relations

end RankOneEpsilonTwist

/-- Moving an arbitrary multiplicative character from the test to the
candidate preserves the full p-adic rank-one epsilon relation. -/
def RankOneEpsilonTwistStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (Langlands.GeneralLinear 1 F.Carrier) V)
    (χ : F.Carrierˣ →* ℂˣ) (e : ℂˣ × ℤ),
    IsPadicPairEpsilonFactor F ψ ν
        (Langlands.twist (χ.comp determinant) π) (rankOneCharacter 1) e ↔
      IsPadicPairEpsilonFactor F ψ ν π (rankOneCharacter χ) e

theorem rankOneEpsilonTwist : RankOneEpsilonTwistStatement.{uF, uV} := by
  intro p hp F ψ ν V hV hVC π χ e
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear 1 F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear 1 F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent 1 F.Carrier)
  let : BorelSpace (upperUnipotent 1 F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient 0 F.Carrier)
  change IsPairEpsilonFactor _ _ _ _ _ _ _ ↔ IsPairEpsilonFactor _ _ _ _ _ _ _
  rw [isPairEpsilonFactor_self, isPairEpsilonFactor_self]
  exact RankOneEpsilonTwist.factor ψ χ
    (normalizedAbsoluteValue F.canonicalTopologicalData) ν π
    F.canonicalTopologicalData.residueCardinality e

/-- The full epsilon relation for two rank-one characters depends only on
their product, without continuity or self-dual-measure hypotheses. -/
theorem isPadicPairEpsilonFactor_rankOneCharacters_mul
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier)
    (χ η : F.Carrierˣ →* ℂˣ) (e : ℂˣ × ℤ) :
    IsPadicPairEpsilonFactor F ψ ν (rankOneCharacter χ) (rankOneCharacter η) e ↔
      IsPadicPairEpsilonFactor F ψ ν (rankOneCharacter (χ * η))
        (rankOneCharacter 1) e := by
  have htwist : Langlands.twist (η.comp determinant) (rankOneCharacter χ) =
      rankOneCharacter (χ * η) := by
    ext g
    simp [rankOneCharacter, characterRepresentation, twist, mul_comm]
  rw [← htwist]
  exact (rankOneEpsilonTwist p F ψ ν (rankOneCharacter χ) η e).symm

end Langlands.RankinSelberg
