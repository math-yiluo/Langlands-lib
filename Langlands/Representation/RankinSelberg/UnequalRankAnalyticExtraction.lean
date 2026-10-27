import Langlands.Representation.RankinSelberg.UnequalRankBilinearComparison
import Langlands.Representation.RankinSelberg.ModelMinusOneScalar

/-!
# Extracting actual continuations from unequal-rank analytic conclusions

The definitions choose continuations only from supplied analytic conclusions.
The block-zero assembly still assumes continued covariant forms and uniqueness.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

section FixedBlock

variable {F : Type uF} [Field F] [TopologicalSpace F]
  [MeasurableSpace F] {n r j k : ℕ} {hr : r = n + (j + k + 1)}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

/-- The continuation clause of the analytic input, with only the rank equality
transported. -/
theorem UnequalRankAnalyticAt.exists_continuation
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule) :
    ∃ R : RationalFunctions, HasRationalContinuation q
      (unequalRankIntegralAt j k hr ψ abv μ ν f.val f'.val) R := by
  subst r
  exact hA.2.1 f f'

/-- A continuation chosen from the actual analytic input at each vector pair.
No continuation existence theorem is asserted by this definition. -/
def UnequalRankAnalyticAt.continuation
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule) : RationalFunctions :=
  Classical.choose (hA.exists_continuation f f')

theorem UnequalRankAnalyticAt.continuation_spec
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule) :
    HasRationalContinuation q
      (unequalRankIntegralAt j k hr ψ abv μ ν f.val f'.val)
      (hA.continuation f f') :=
  Classical.choose_spec (hA.exists_continuation f f')

/-- Normalized-generator existence forces a nonzero member of the actual
fixed-block rational-value set. -/
theorem UnequalRankAnalyticAt.exists_ne_zero
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ') :
    ∃ R ∈ unequalRankValuesAt j k hr q ψ abv μ ν π σ ℓ ℓ', R ≠ 0 := by
  subst r
  obtain ⟨P, hP⟩ := hA.2.2.2
  exact hP.exists_ne_zero

/-- For q > 1, uniqueness of actual continuations transfers the nonzero
value-set witness to the chosen continuation family. -/
theorem UnequalRankAnalyticAt.exists_continuation_ne_zero
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ') (hq : 1 < q) :
    ∃ f f', hA.continuation f f' ≠ 0 := by
  obtain ⟨R, hR, hRne⟩ := hA.exists_ne_zero
  rw [unequalRankValuesAt_eq_set] at hR
  obtain ⟨f, f', hR⟩ := hR
  refine ⟨f, f', ?_⟩
  rw [(hA.continuation_spec f f').unique hq hR]
  exact hRne

end FixedBlock

section BlockZero

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F]
  [MeasurableSpace F] {n r : ℕ} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)} {ν : AdditiveHaarMeasure F}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ} {hnr : n < r}

/-- Exact fixed-data block-zero assembly from the two supplied analytic inputs,
continued covariant forms and fixed-data uniqueness. The minus-one scalar and
separate nonzero continuation witnesses are derived, not extra premises. -/
theorem exists_blockZeroGammaEquation_of_analytic
    (hq : 1 < q)
    (hσ : IsOfWhittakerType n (inverseStandardCharacter ψ n) σ)
    (hA : UnequalRankAnalyticAt 0 (r - n - 1) (by omega) q ψ abv μ
      (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ')
    (hAd : UnequalRankAnalyticAt (r - n - 1) 0 (by omega) q (ψ.scale (-1)) abv μ
      (rectangularMeasure ν (r - n - 1) (n + 1))
      (inverseTransposePullback π) (inverseTransposePullback σ)
      (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ'))
    (hforms : UnequalRankBlockZeroContinuedFormsConclusion hnr q ψ abv μ ν π σ ℓ ℓ')
    (hunique : UnequalRankBilinearUniquenessConclusion hnr q ψ abv π σ ℓ ℓ') :
    ∃ G : RationalFunctions, G ≠ 0 ∧
      UnequalRankBlockZeroGammaEquation hnr q ψ abv μ ν π σ ℓ ℓ' G := by
  let R := hA.continuation
  let e := translatedFirstDualModelEquiv ψ π ℓ (blockWeylAt n r hnr)
  let e' := secondDualModelMap ψ σ ℓ'
  let Rd := fun f f' => hAd.continuation (e f) (e' f')
  have hR := hA.continuation_spec
  have hRd : ∀ f f', HasRationalContinuation q
      (dualUnequalRankModelIntegralAt hnr 0 (r - n - 1) (by omega)
        ψ abv μ ν π σ ℓ ℓ' f f') (Rd f f') := by
    intro f f'
    exact hAd.continuation_spec (e f) (e' f')
  have hRne : ∃ f f', R f f' ≠ 0 := hA.exists_continuation_ne_zero hq
  have hRdne : ∃ f f', Rd f f' ≠ 0 := by
    obtain ⟨g, g', hg⟩ := hAd.exists_continuation_ne_zero hq
    obtain ⟨f, hf⟩ := e.surjective g
    obtain ⟨f', hf'⟩ := (secondDualModelMap_bijective ψ σ ℓ').surjective g'
    refine ⟨f, f', ?_⟩
    dsimp [Rd]
    rw [hf, hf']
    exact hg
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let δ : ℂˣ := Units.mk0 (q : ℂ)⁻¹ (inv_ne_zero hq0)
  exact hforms.exists_gammaEquation hunique hq δ (modelMinusOneScalar σ hσ) rfl
    (hasModelMinusOneScalar_modelMinusOneScalar σ hσ ℓ') R Rd hR hRd hRne hRdne

end BlockZero

end Langlands.RankinSelberg
