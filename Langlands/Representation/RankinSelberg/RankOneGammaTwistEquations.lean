import Langlands.Representation.RankinSelberg.RankOneGammaTwistIntegrals
import Langlands.Representation.RankinSelberg.EqualRankSwapEquations

noncomputable section

namespace Langlands.RankinSelberg.RankOneGammaTwist

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV

section Equations

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient 0 F))
  {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (ℓ : glFunctionals ψ n π) (ellC : ℂ →ₗ[ℂ] ℂ)

omit [IsTopologicalRing F] in
/-- All continuations in each forward block family agree. -/
theorem unequal_values (j k : ℕ) (hr : n = 0 + (j + k + 1)) (q : ℕ)
    (ν : Measure (Matrix (Fin j) (Fin 1) F)) :
    unequalRankValuesAt j k hr q ψ abv μ ν (Langlands.twist (χ.comp determinant) π)
      (rankOneCharacter 1) (candidateFunctional ψ χ π ℓ) (testFunctional ψ 1 ellC) =
    unequalRankValuesAt j k hr q ψ abv μ ν π (rankOneCharacter χ) ℓ
      (testFunctional ψ χ ellC) := by
  ext R
  rw [unequalRankValuesAt_eq, unequalRankValuesAt_eq]
  constructor
  · rintro ⟨f, f', hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, by
      rwa [unequal_forward ψ χ abv μ π ℓ ellC v z j k hr ν] at hR⟩
  · rintro ⟨f, f', hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, by
      rwa [← unequal_forward ψ χ abv μ π ℓ ellC v z j k hr ν] at hR⟩

/-- The fixed-functional gamma equation transports with its nonzero witnesses. -/
theorem unequal_equation (hn : 0 < n) (ν : AdditiveHaarMeasure F)
    (q : ℕ) (G : RationalFunctions) (hC : ellC ≠ 0) :
    UnequalRankGammaEquation hn q ψ abv μ ν (Langlands.twist (χ.comp determinant) π)
      (rankOneCharacter 1) (candidateFunctional ψ χ π ℓ) (testFunctional ψ 1 ellC) G ↔
    UnequalRankGammaEquation hn q ψ abv μ ν π (rankOneCharacter χ) ℓ
      (testFunctional ψ χ ellC) G := by
  have hsq : χ (-1) ^ 2 = 1 := character_negOne_sq χ
  have hsqC : (χ (-1) : ℂ) * (χ (-1) : ℂ) = 1 := by
    simpa only [pow_two, Units.val_mul, Units.val_one] using congrArg Units.val hsq
  constructor
  · rintro ⟨ζ, hζ, hall⟩
    have hζ1 : ζ = 1 := by
      simpa only [MonoidHom.one_apply] using
        HasModelMinusOneScalar.unique hC hζ (test_minusOne ψ 1 ellC)
    subst ζ
    refine ⟨χ (-1), test_minusOne ψ χ ellC, ?_⟩
    intro j k hr
    obtain ⟨hnonzero, hFE⟩ := hall j k hr
    refine ⟨?_, ?_⟩
    · rwa [unequal_values ψ χ abv μ π ℓ ellC j k hr q] at hnonzero
    · intro f f'
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨R, Rd, hR, hRd, heq⟩ := hFE (modelMap _ _ v) (modelMap _ _ z)
      refine ⟨R, RatFunc.C ((χ (-1) : ℂ) ^ n) * Rd, ?_, ?_, ?_⟩
      · rwa [unequal_forward ψ χ abv μ π ℓ ellC v z j k hr] at hR
      · have hd := hasRationalContinuation_const_mul ((χ (-1) : ℂ) ^ n) hRd
        have hi : (fun s => (χ (-1) : ℂ) ^ n *
            dualUnequalRankModelIntegralAt hn j k hr ψ abv μ ν
              (Langlands.twist (χ.comp determinant) π) (rankOneCharacter 1)
              (candidateFunctional ψ χ π ℓ) (testFunctional ψ 1 ellC)
              (modelMap _ _ v) (modelMap _ _ z) s) =
            dualUnequalRankModelIntegralAt hn j k hr ψ abv μ ν π (rankOneCharacter χ)
              ℓ (testFunctional ψ χ ellC) (modelMap _ _ v) (modelMap _ _ z) := by
          rw [unequal_dual ψ χ abv μ π ℓ ellC v z hn j k hr ν]
          funext s
          simp only [← mul_assoc, ← mul_pow, hsqC, one_pow, one_mul]
        rwa [hi] at hd
      · simpa only [Units.val_one, one_pow, mul_one] using
          GammaFunctionalEquation.negOne_swap (α := χ (-1)) (by simp) heq
  · rintro ⟨ζ, hζ, hall⟩
    have hζχ : ζ = χ (-1) :=
      HasModelMinusOneScalar.unique hC hζ (test_minusOne ψ χ ellC)
    subst ζ
    refine ⟨1, by simpa only [MonoidHom.one_apply] using test_minusOne ψ 1 ellC, ?_⟩
    intro j k hr
    obtain ⟨hnonzero, hFE⟩ := hall j k hr
    refine ⟨?_, ?_⟩
    · rwa [← unequal_values ψ χ abv μ π ℓ ellC j k hr q] at hnonzero
    · intro f f'
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨R, Rd, hR, hRd, heq⟩ := hFE (modelMap _ _ v) (modelMap _ _ z)
      refine ⟨R, RatFunc.C ((χ (-1) : ℂ) ^ n) * Rd, ?_, ?_, ?_⟩
      · rwa [← unequal_forward ψ χ abv μ π ℓ ellC v z j k hr] at hR
      · rw [unequal_dual ψ χ abv μ π ℓ ellC v z hn j k hr ν]
        exact hasRationalContinuation_const_mul _ hRd
      · simpa only [Units.val_one, one_pow, one_mul] using
          GammaFunctionalEquation.negOne_swap (α := 1) hsq heq

end Equations

section EqualEquations

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] [MeasurableSpace (LeftUnipotentQuotient 0 F)]
  (ψ : UnitaryAdditiveCharacter F) (χ : Fˣ →* ℂˣ) (abv : AbsoluteValue F ℝ)
  (μ : Measure (LeftUnipotentQuotient 0 F))
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (Langlands.GeneralLinear 1 F) V)
  (ℓ : glFunctionals ψ 0 π) (ellC : ℂ →ₗ[ℂ] ℂ)

omit [IsTopologicalRing F] [MeasurableSpace F] in
/-- The equal-rank continuation family agrees with all Schwartz--Bruhat tests. -/
theorem equal_values (q : ℕ) :
    equalRankRationalValues q ψ abv μ (Langlands.twist (χ.comp determinant) π)
      (rankOneCharacter 1) (candidateFunctional ψ χ π ℓ) (testFunctional ψ 1 ellC) =
    equalRankRationalValues q ψ abv μ π (rankOneCharacter χ) ℓ
      (testFunctional ψ χ ellC) := by
  ext R
  constructor
  · rintro ⟨f, f', Φ, hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, Φ, by
      rwa [equal_forward ψ χ abv μ ellC z π ℓ v Φ] at hR⟩
  · rintro ⟨f, f', Φ, hR⟩
    obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
    obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
    exact ⟨modelMap _ _ v, modelMap _ _ z, Φ, by
      rwa [← equal_forward ψ χ abv μ ellC z π ℓ v Φ] at hR⟩

/-- The rank-one equation keeps the same Fourier pair and continuations. -/
theorem equal_equation (ν : AdditiveHaarMeasure F) (q : ℕ) (G : RationalFunctions) :
    EqualRankGammaEquation q ψ abv μ ν (Langlands.twist (χ.comp determinant) π)
      (rankOneCharacter 1) (candidateFunctional ψ χ π ℓ) (testFunctional ψ 1 ellC) G ↔
    EqualRankGammaEquation q ψ abv μ ν π (rankOneCharacter χ) ℓ
      (testFunctional ψ χ ellC) G := by
  constructor
  · rintro ⟨ζ, -, hnonzero, hFE⟩
    refine ⟨χ (-1), test_minusOne ψ χ ellC, ?_, ?_⟩
    · rwa [equal_values ψ χ abv μ π ℓ ellC q] at hnonzero
    · intro f f' Φ
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨Φhat, R, Rd, hFourier, hR, hRd, heq⟩ :=
        hFE (modelMap _ _ v) (modelMap _ _ z) Φ
      refine ⟨Φhat, R, Rd, hFourier, ?_, ?_, ?_⟩
      · rwa [equal_forward ψ χ abv μ ellC z π ℓ v Φ] at hR
      · rwa [equal_dual ψ χ abv μ ellC z π ℓ v Φhat] at hRd
      · simpa only [GammaFunctionalEquation, pow_zero] using heq
  · rintro ⟨ζ, -, hnonzero, hFE⟩
    refine ⟨1, by simpa only [MonoidHom.one_apply] using test_minusOne ψ 1 ellC, ?_, ?_⟩
    · rwa [← equal_values ψ χ abv μ π ℓ ellC q] at hnonzero
    · intro f f' Φ
      obtain ⟨v, rfl⟩ := modelMap_surjective _ _ f
      obtain ⟨z, rfl⟩ := modelMap_surjective _ _ f'
      obtain ⟨Φhat, R, Rd, hFourier, hR, hRd, heq⟩ :=
        hFE (modelMap _ _ v) (modelMap _ _ z) Φ
      refine ⟨Φhat, R, Rd, hFourier, ?_, ?_, ?_⟩
      · rwa [← equal_forward ψ χ abv μ ellC z π ℓ v Φ] at hR
      · rwa [← equal_dual ψ χ abv μ ellC z π ℓ v Φhat] at hRd
      · simpa only [GammaFunctionalEquation, pow_zero] using heq

end EqualEquations

end Langlands.RankinSelberg.RankOneGammaTwist
