import Langlands.Representation.RankinSelberg.EqualRankSwapModels

/-! Fixed-character equal-rank integral transport, retaining the Fourier tests. -/

noncomputable section

namespace Langlands.RankinSelberg

open Whittaker GeneralLinear HarmonicAnalysis MeasureTheory

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  [BorelSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))
  (hμ : HasCharacterChangeMeasureLaw abv (-1) μ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
  (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
  (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)

include hμ

/-- Exchange the two translated model vectors at the original character.
The original integral and its test function are preserved. -/
theorem equalRankModelIntegral_negOne_swap
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankModelIntegral ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)
        (negOneStandardModelVector ψ σ ℓ' f') (negOneInverseModelVector ψ π ℓ f) Φ s =
      equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ s := by
  have hI : equalRankIntegrand ψ abv
        (negOneStandardModelVector ψ σ ℓ' f').val
        (negOneInverseModelVector ψ π ℓ f).val Φ s =
      fun q => equalRankIntegrand ψ abv f.val f'.val Φ s
        (characterChangeQuotient (-1) n q) := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [equalRankIntegrand_mk, characterChangeQuotient_mk,
        negOneStandardModelVector_apply, negOneInverseModelVector_apply,
        lastRow_characterChangeElement_mul, determinantWeight_mul,
        determinantWeight_characterChangeElement_neg_one, one_mul]
      ring
  change (∫ q, equalRankIntegrand ψ abv
    (negOneStandardModelVector ψ σ ℓ' f').val
    (negOneInverseModelVector ψ π ℓ f).val Φ s q ∂μ) = _
  rw [hI, integral_characterChangeQuotient abv (-1) μ hμ]
  simp only [characterChangeModulus_neg_one, NNReal.coe_one, one_smul]
  rfl

/-- The same exchange on actual dual model integrals multiplies by the
product of the `n`-th powers of the two minus-one scalars. -/
theorem dualEqualRankModelIntegral_negOne_swap
    {α β : ℂˣ} (hα : HasModelMinusOneScalar π ℓ α)
    (hβ : HasModelMinusOneScalar σ ℓ' β)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    dualEqualRankModelIntegral ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)
        (negOneStandardModelVector ψ σ ℓ' f') (negOneInverseModelVector ψ π ℓ f) Φ s =
      ((α : ℂ) ^ n * (β : ℂ) ^ n) *
        dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ s := by
  have hI : equalRankIntegrand (ψ.scale (-1)) abv
        (firstDualFunction ψ n (negOneStandardModelVector ψ σ ℓ' f').val)
        (secondDualFunction ψ n (negOneInverseModelVector ψ π ℓ f).val) Φ s =
      fun q => ((α : ℂ) ^ n * (β : ℂ) ^ n) *
        equalRankIntegrand (ψ.scale (-1)) abv
          (firstDualFunction ψ n f.val) (secondDualFunction ψ n f'.val) Φ s
          (characterChangeQuotient (-1) n q) := by
    funext q
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [equalRankIntegrand_mk, characterChangeQuotient_mk,
        firstDualFunction_apply, secondDualFunction_apply,
        negOneStandardModelVector_apply, negOneInverseModelVector_apply,
        lastRow_characterChangeElement_mul, determinantWeight_mul,
        determinantWeight_characterChangeElement_neg_one, one_mul]
      rw [hα.negOne_dual_apply, hβ.negOne_dual_apply]
      ring
  change (∫ q, equalRankIntegrand (ψ.scale (-1)) abv
    (firstDualFunction ψ n (negOneStandardModelVector ψ σ ℓ' f').val)
    (secondDualFunction ψ n (negOneInverseModelVector ψ π ℓ f).val) Φ s q ∂μ) = _
  rw [hI, integral_const_mul, integral_characterChangeQuotient abv (-1) μ hμ]
  simp only [characterChangeModulus_neg_one, NNReal.coe_one, one_smul]
  rfl

/-- Original rational-value sets are identical after the translated exchange;
no convergence or analytic existence theorem is assumed. -/
theorem equalRankRationalValues_negOne_swap (q : ℕ) :
    equalRankRationalValues q ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ) =
      equalRankRationalValues q ψ abv μ π σ ℓ ℓ' := by
  ext R
  constructor
  · rintro ⟨g, g', Φ, hR⟩
    obtain ⟨f', rfl⟩ := negOneStandardModelVector_surjective ψ σ ℓ' g
    obtain ⟨f, rfl⟩ := negOneInverseModelVector_surjective ψ π ℓ g'
    refine ⟨f, f', Φ, ?_⟩
    have hi : equalRankModelIntegral ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)
        (negOneStandardModelVector ψ σ ℓ' f') (negOneInverseModelVector ψ π ℓ f) Φ =
      equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ := by
      funext s
      exact equalRankModelIntegral_negOne_swap ψ abv μ hμ π σ ℓ ℓ' f f' Φ s
    rwa [hi] at hR
  · rintro ⟨f, f', Φ, hR⟩
    refine ⟨negOneStandardModelVector ψ σ ℓ' f', negOneInverseModelVector ψ π ℓ f, Φ, ?_⟩
    have hi : equalRankModelIntegral ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)
        (negOneStandardModelVector ψ σ ℓ' f') (negOneInverseModelVector ψ π ℓ f) Φ =
      equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ := by
      funext s
      exact equalRankModelIntegral_negOne_swap ψ abv μ hμ π σ ℓ ℓ' f f' Φ s
    rwa [hi]

/-- The original continuation is retained by the translated exchange. -/
theorem hasRationalContinuation_equalRank_negOne_swap {q : ℕ} {R : RationalFunctions}
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hR : HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R) :
    HasRationalContinuation q
      (equalRankModelIntegral ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)
        (negOneStandardModelVector ψ σ ℓ' f') (negOneInverseModelVector ψ π ℓ f) Φ) R := by
  have hi : equalRankModelIntegral ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)
        (negOneStandardModelVector ψ σ ℓ' f') (negOneInverseModelVector ψ π ℓ f) Φ =
      equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ :=
    funext (equalRankModelIntegral_negOne_swap ψ abv μ hμ π σ ℓ ℓ' f f' Φ)
  rwa [hi]

/-- The dual continuation gains the same constant as the actual dual integral. -/
theorem hasRationalContinuation_dualEqualRank_negOne_swap
    {q : ℕ} {R : RationalFunctions} {α β : ℂˣ}
    (hα : HasModelMinusOneScalar π ℓ α) (hβ : HasModelMinusOneScalar σ ℓ' β)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F))
    (hR : HasRationalContinuation q
      (dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R) :
    HasRationalContinuation q
      (dualEqualRankModelIntegral ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)
        (negOneStandardModelVector ψ σ ℓ' f') (negOneInverseModelVector ψ π ℓ f) Φ)
      (RatFunc.C ((α : ℂ) ^ n * (β : ℂ) ^ n) * R) := by
  have hi : dualEqualRankModelIntegral ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)
        (negOneStandardModelVector ψ σ ℓ' f') (negOneInverseModelVector ψ π ℓ f) Φ =
      fun s => ((α : ℂ) ^ n * (β : ℂ) ^ n) *
        dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ s :=
    funext (dualEqualRankModelIntegral_negOne_swap ψ abv μ hμ π σ ℓ ℓ' hα hβ f f' Φ)
  rw [hi]
  exact hasRationalContinuation_const_mul _ hR

/-- Nonzero constant multiplication preserves the Laurent span of dual values. -/
theorem zetaSpan_dualEqualRankRationalValues_negOne_swap (q : ℕ) {α β : ℂˣ}
    (hα : HasModelMinusOneScalar π ℓ α) (hβ : HasModelMinusOneScalar σ ℓ' β) :
    zetaSpan (dualEqualRankRationalValues q ψ abv μ σ π
        (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)) =
      zetaSpan (dualEqualRankRationalValues q ψ abv μ π σ ℓ ℓ') := by
  let κ : ℂ := (α : ℂ) ^ n * (β : ℂ) ^ n
  have hκ : κ ≠ 0 := mul_ne_zero (pow_ne_zero _ α.ne_zero) (pow_ne_zero _ β.ne_zero)
  symm
  apply zetaSpan_eq_of_const_mul hκ
  · rintro R ⟨f, f', Φ, hR⟩
    exact ⟨negOneStandardModelVector ψ σ ℓ' f', negOneInverseModelVector ψ π ℓ f, Φ,
      hasRationalContinuation_dualEqualRank_negOne_swap ψ abv μ hμ π σ ℓ ℓ'
        hα hβ f f' Φ hR⟩
  · rintro R ⟨g, g', Φ, hR⟩
    obtain ⟨f', rfl⟩ := negOneStandardModelVector_surjective ψ σ ℓ' g
    obtain ⟨f, rfl⟩ := negOneInverseModelVector_surjective ψ π ℓ g'
    refine ⟨f, f', Φ, ?_⟩
    have hi : (fun s => κ⁻¹ * dualEqualRankModelIntegral ψ abv μ σ π
          (negOneStandardFunctional ψ σ ℓ') (negOneInverseFunctional ψ π ℓ)
          (negOneStandardModelVector ψ σ ℓ' f') (negOneInverseModelVector ψ π ℓ f) Φ s) =
        dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ := by
      funext s
      rw [dualEqualRankModelIntegral_negOne_swap ψ abv μ hμ π σ ℓ ℓ' hα hβ,
        ← mul_assoc, inv_mul_cancel₀ hκ, one_mul]
    simpa only [hi] using hasRationalContinuation_const_mul κ⁻¹ hR

end Langlands.RankinSelberg
