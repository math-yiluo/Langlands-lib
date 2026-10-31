import Langlands.Representation.RankinSelberg.RankOneGammaTwistEquations

/-! Transport of the full gamma certificate, including every measure and functional. -/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

namespace RankOneGammaTwist

section Relations

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] [MeasurableSpace F]
  [MeasurableSpace (Langlands.GeneralLinear 1 F)]
  [BorelSpace (Langlands.GeneralLinear 1 F)]
  [MeasurableSpace (upperUnipotent 1 F)] [BorelSpace (upperUnipotent 1 F)]
  [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ) (abv : AbsoluteValue F ℝ)
  (ν : AdditiveHaarMeasure F)
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)

/-- The full unequal-rank relation transports all measures and nonzero functionals. -/
theorem unequal_factor (hn : 0 < n) (q : ℕ) (G : RationalFunctions) :
    IsUnequalRankGammaFactor hn q ψ abv ν (Langlands.twist (χ.comp determinant) π)
      (rankOneCharacter 1) G ↔
    IsUnequalRankGammaFactor hn q ψ abv ν π (rankOneCharacter χ) G := by
  constructor
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    let L := untwistFunctional _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) π ℓ
    refine ⟨hμ, ⟨L, hℓ⟩, ⟨testFunctional ψ χ ℓ'.val, hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    exact (unequal_equation ψ χ abv μ π L₀ L₀'.val hn ν q G hL₀').mp
      (@hall hinv μ hμc (candidateFunctional ψ χ π L₀)
        (testFunctional ψ 1 L₀'.val) hL₀ hL₀')
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    refine ⟨hμ, ⟨candidateFunctional ψ χ π ℓ, hℓ⟩,
      ⟨testFunctional ψ 1 ℓ'.val, hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    let L := untwistFunctional _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) π L₀
    exact (unequal_equation ψ χ abv μ π L L₀'.val hn ν q G hL₀').mpr
      (@hall hinv μ hμc L (testFunctional ψ χ L₀'.val) hL₀ hL₀')

/-- The full rank-one equal-rank relation retains all measures and Fourier data. -/
theorem equal_factor
    {U : Type uV} [AddCommGroup U] [Module ℂ U]
    (ρ : Representation ℂ (Langlands.GeneralLinear 1 F) U) (q : ℕ) (G : RationalFunctions) :
    IsEqualRankGammaFactor q ψ abv ν (Langlands.twist (χ.comp determinant) ρ)
      (rankOneCharacter 1) G ↔
    IsEqualRankGammaFactor q ψ abv ν ρ (rankOneCharacter χ) G := by
  constructor
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    let L := untwistFunctional _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) ρ ℓ
    refine ⟨hμ, ⟨L, hℓ⟩, ⟨testFunctional ψ χ ℓ'.val, hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    exact (equal_equation ψ χ abv μ ρ L₀ L₀'.val ν q G).mp
      (@hall hinv μ hμc (candidateFunctional ψ χ ρ L₀)
        (testFunctional ψ 1 L₀'.val) hL₀ hL₀')
  · rintro ⟨hμ, ⟨ℓ, hℓ⟩, ⟨ℓ', hℓ'⟩, hall⟩
    refine ⟨hμ, ⟨candidateFunctional ψ χ ρ ℓ, hℓ⟩,
      ⟨testFunctional ψ 1 ℓ'.val, hℓ'⟩, ?_⟩
    intro hinv μ hμc L₀ L₀' hL₀ hL₀'
    let L := untwistFunctional _ _ (χ.comp determinant)
      (determinantCharacter_unipotent χ) ρ L₀
    exact (equal_equation ψ χ abv μ ρ L L₀'.val ν q G).mpr
      (@hall hinv μ hμc L (testFunctional ψ χ L₀'.val) hL₀ hL₀')

/-- Both rank branches of the original pair relation, including its rank cast. -/
theorem pair_factor (q : ℕ) (G : RationalFunctions) :
    IsPairGammaFactor q ψ abv ν (Langlands.twist (χ.comp determinant) π)
      (rankOneCharacter 1) G ↔
    IsPairGammaFactor q ψ abv ν π (rankOneCharacter χ) G := by
  by_cases hn : 0 < n
  · rw [isPairGammaFactor_of_lt hn, isPairGammaFactor_of_lt hn]
    exact unequal_factor ψ χ abv ν π hn q G
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    subst n
    rw [isPairGammaFactor_self, isPairGammaFactor_self]
    exact equal_factor ψ χ abv ν π q G

end Relations

end RankOneGammaTwist

/-- Rank-one determinant twists transport the unchanged full gamma certificate. -/
theorem rankOneGammaTwist : RankOneGammaTwistStatement.{uF, uV} := by
  intro p hp F ψ ν n V hV hVC π χ G
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
  simp only [IsPadicSymmetricGammaFactor, Nat.zero_le, ite_true]
  exact RankOneGammaTwist.pair_factor ψ χ
    (normalizedAbsoluteValue F.canonicalTopologicalData) ν π
    F.canonicalTopologicalData.residueCardinality G

end Langlands.RankinSelberg
