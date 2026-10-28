import Langlands.Representation.RankinSelberg.UnequalRankBlockZeroIntegralLaws
import Langlands.Representation.RankinSelberg.UnequalRankBilinearUniquenessStatement
import Langlands.Representation.RankinSelberg.UnequalRankGammaFactor
import Langlands.Representation.RankinSelberg.LaurentEvaluation
import Langlands.Representation.RankinSelberg.RationalEvaluation

/-!
# Bilinear continuation families of the unequal-rank integrals

Under an unequal-rank analytic input, the unique rational continuations of the
actual integrals form a bilinear map. Pointwise evaluation of such a family at a
point where all of its values are regular is a bilinear form. If one integral is
a monomial multiple of another for every `s`, so are their continuations;
`UnequalRankBlockZeroCovariance` applies this to JPSS (2.11.2) and (2.11.4).
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open RationalContinuationLinear RationalEvaluation

universe uF uV uW

section Evaluation

variable {M : Type*} {M' : Type*} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']

theorem regularAt_C (c z : ℂ) : RegularAt (RatFunc.C c : RationalFunctions) z := by
  simp [RegularAt]

theorem eval_smul_of_regularAt {z : ℂ} {R : RationalFunctions} (hR : RegularAt R z) (c : ℂ) :
    RatFunc.eval (RingHom.id ℂ) z (c • R) = c * RatFunc.eval (RingHom.id ℂ) z R := by
  rw [RatFunc.smul_eq_C_mul, eval_mul (regularAt_C c z) hR, RatFunc.eval_C]
  rfl

/-- A rational function cleared by a polynomial `P` into a Laurent polynomial is
regular at every nonzero point where `P` does not vanish. -/
theorem regularAt_of_clears {z : ℂ} (hz : z ≠ 0) {P : Polynomial ℂ} (hP : P.eval z ≠ 0)
    {R : RationalFunctions} {a : LaurentCoefficients}
    (ha : laurentToRatFunc a = algebraMap (Polynomial ℂ) RationalFunctions P * R) :
    RegularAt R z := by
  have hP0 : algebraMap (Polynomial ℂ) RationalFunctions P ≠ 0 :=
    RatFunc.algebraMap_ne_zero (fun h => hP (by simp [h]))
  have hR : R = laurentToRatFunc a * (algebraMap (Polynomial ℂ) RationalFunctions P)⁻¹ := by
    rw [ha, mul_comm (algebraMap _ _ P) R, mul_inv_cancel_right₀ hP0]
  rw [hR]
  exact (show RegularAt (laurentToRatFunc a) z from laurentToRatFunc_regular (Units.mk0 z hz) a).mul
    (RegularAt.inv (by rw [RatFunc.eval_algebraMap]; exact hP))

/-- Evaluation of a monomial multiple at a nonzero regular point. -/
theorem eval_C_mul_X_zpow_mul {z : ℂ} (hz : z ≠ 0) {R : RationalFunctions}
    (hR : RegularAt R z) (c : ℂ) (m : ℤ) :
    RatFunc.eval (RingHom.id ℂ) z (RatFunc.C c * RatFunc.X ^ m * R) =
      c * z ^ m * RatFunc.eval (RingHom.id ℂ) z R := by
  have hX : RatFunc.eval (RingHom.id ℂ) z (RatFunc.X : RationalFunctions) ≠ 0 := by
    rw [RatFunc.eval_X]; exact hz
  rw [eval_mul ((regularAt_C c z).mul (RegularAt.zpow hX m)) hR,
    eval_mul (regularAt_C c z) (RegularAt.zpow hX m), eval_zpow hX, RatFunc.eval_C,
    RatFunc.eval_X]
  rfl

/-- Pointwise evaluation of a bilinear family of rational functions at a point
where all of its values are regular. -/
def evalForm (C : M →ₗ[ℂ] M' →ₗ[ℂ] RationalFunctions) (z : ℂ)
    (hreg : ∀ f f', RegularAt (C f f') z) : M →ₗ[ℂ] M' →ₗ[ℂ] ℂ :=
  LinearMap.mk₂ ℂ (fun f f' => RatFunc.eval (RingHom.id ℂ) z (C f f'))
    (fun f₁ f₂ f' => by
      simp only [map_add, LinearMap.add_apply]
      exact eval_add (hreg f₁ f') (hreg f₂ f'))
    (fun c f f' => by
      simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
      exact eval_smul_of_regularAt (hreg f f') c)
    (fun f f'₁ f'₂ => by
      simp only [map_add]
      exact eval_add (hreg f f'₁) (hreg f f'₂))
    (fun c f f' => by
      simp only [map_smul, smul_eq_mul]
      exact eval_smul_of_regularAt (hreg f f') c)

@[simp] theorem evalForm_apply (C : M →ₗ[ℂ] M' →ₗ[ℂ] RationalFunctions) (z : ℂ)
    (hreg : ∀ f f', RegularAt (C f f') z) (f : M) (f' : M') :
    evalForm C z hreg f f' = RatFunc.eval (RingHom.id ℂ) z (C f f') := rfl

end Evaluation

section Family

variable {F : Type uF} [Field F] [TopologicalSpace F] [MeasurableSpace F]
  {n r j k : ℕ} {hr : r = n + (j + k + 1)} [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {ν : Measure (Matrix (Fin j) (Fin (n + 1)) F)}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ r π} {ℓ' : glInverseFunctionals ψ n σ}

private theorem exists_blockValue (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    ∃ R : RationalFunctions,
      HasRationalContinuation q (unequalRankIntegralAt j k hr ψ abv μ ν f.val f'.val) R := by
  subst hr
  exact hA.2.1 f f'

/-- The rational continuation chosen for one pair of model vectors. -/
private def blockValue (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    RationalFunctions :=
  Classical.choose (exists_blockValue hA f f')

private theorem blockValue_spec (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    HasRationalContinuation q (unequalRankIntegralAt j k hr ψ abv μ ν f.val f'.val)
      (blockValue hA f f') :=
  Classical.choose_spec (exists_blockValue hA f f')

private theorem blockValue_eq (hq : 1 < q) (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    {f : (coefficientModel π ℓ).toSubmodule} {f' : (coefficientModel σ ℓ').toSubmodule}
    {R : RationalFunctions}
    (hR : HasRationalContinuation q (unequalRankIntegralAt j k hr ψ abv μ ν f.val f'.val) R) :
    blockValue hA f f' = R :=
  (blockValue_spec hA f f').unique hq hR

private theorem continuation_smul' {c : ℂ} {I J : ℂ → ℂ} {R : RationalFunctions}
    (hR : HasRationalContinuation q I R) (hIJ : ∀ s, J s = c * I s) :
    HasRationalContinuation q J (c • R) := by
  rw [RatFunc.smul_eq_C_mul]
  exact continuation_of_eq_on_right (hasRationalContinuation_const_mul c hR)
    ⟨0, fun s _ => hIJ s⟩

private theorem integralAt_add_left [SFinite μ] [SFinite ν]
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (f₁ f₂ : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      unequalRankIntegralAt j k hr ψ abv μ ν (f₁ + f₂).val f'.val s =
        unequalRankIntegralAt j k hr ψ abv μ ν f₁.val f'.val s +
          unequalRankIntegralAt j k hr ψ abv μ ν f₂.val f'.val s := by
  subst hr
  obtain ⟨a₁, h₁⟩ := hA.1 f₁ f'
  obtain ⟨a₂, h₂⟩ := hA.1 f₂ f'
  exact ⟨max a₁ a₂, fun s hs => unequalRankIntegral_add_left ψ abv j k μ ν
    (h₁ s ((le_max_left _ _).trans_lt hs)) (h₂ s ((le_max_right _ _).trans_lt hs))⟩

private theorem integralAt_add_right [SFinite μ] [SFinite ν]
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f'₁ f'₂ : (coefficientModel σ ℓ').toSubmodule) :
    ∃ b : ℝ, ∀ s : ℂ, b < s.re →
      unequalRankIntegralAt j k hr ψ abv μ ν f.val (f'₁ + f'₂).val s =
        unequalRankIntegralAt j k hr ψ abv μ ν f.val f'₁.val s +
          unequalRankIntegralAt j k hr ψ abv μ ν f.val f'₂.val s := by
  subst hr
  obtain ⟨a₁, h₁⟩ := hA.1 f f'₁
  obtain ⟨a₂, h₂⟩ := hA.1 f f'₂
  exact ⟨max a₁ a₂, fun s hs => unequalRankIntegral_add_right ψ abv j k μ ν
    (h₁ s ((le_max_left _ _).trans_lt hs)) (h₂ s ((le_max_right _ _).trans_lt hs))⟩

private theorem integralAt_smul_left (c : ℂ) (W₁ : WhittakerFunctions ψ r)
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegralAt j k hr ψ abv μ ν (c • W₁) W' s =
      c * unequalRankIntegralAt j k hr ψ abv μ ν W₁ W' s := by
  subst hr
  exact unequalRankIntegral_smul_left ψ abv j k μ ν c W₁ W' s

private theorem integralAt_smul_right (c : ℂ) (W₁ : WhittakerFunctions ψ r)
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegralAt j k hr ψ abv μ ν W₁ (c • W') s =
      c * unequalRankIntegralAt j k hr ψ abv μ ν W₁ W' s := by
  subst hr
  exact unequalRankIntegral_smul_right ψ abv j k μ ν c W₁ W' s

/-- The bilinear family of rational continuations of the transported unequal-rank
integrals. Its value at `(f, f')` is the unique rational continuation. -/
def blockContinuationFamily (hq : 1 < q) [SFinite μ] [SFinite ν]
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ') :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ] (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ]
      RationalFunctions :=
  LinearMap.mk₂ ℂ (blockValue hA)
    (fun f₁ f₂ f' => blockValue_eq hq hA (continuation_of_eq_on_right
      (continuation_add (blockValue_spec hA f₁ f') (blockValue_spec hA f₂ f'))
      (integralAt_add_left hA f₁ f₂ f')))
    (fun c f f' => blockValue_eq hq hA (continuation_smul' (blockValue_spec hA f f')
      (fun s => integralAt_smul_left c f.val f'.val s)))
    (fun f f'₁ f'₂ => blockValue_eq hq hA (continuation_of_eq_on_right
      (continuation_add (blockValue_spec hA f f'₁) (blockValue_spec hA f f'₂))
      (integralAt_add_right hA f f'₁ f'₂)))
    (fun c f f' => blockValue_eq hq hA (continuation_smul' (blockValue_spec hA f f')
      (fun s => integralAt_smul_right c f.val f'.val s)))

theorem blockContinuationFamily_spec (hq : 1 < q) [SFinite μ] [SFinite ν]
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    HasRationalContinuation q (unequalRankIntegralAt j k hr ψ abv μ ν f.val f'.val)
      (blockContinuationFamily hq hA f f') :=
  blockValue_spec hA f f'

theorem blockContinuationFamily_eq (hq : 1 < q) [SFinite μ] [SFinite ν]
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    {f : (coefficientModel π ℓ).toSubmodule} {f' : (coefficientModel σ ℓ').toSubmodule}
    {R : RationalFunctions}
    (hR : HasRationalContinuation q (unequalRankIntegralAt j k hr ψ abv μ ν f.val f'.val) R) :
    blockContinuationFamily hq hA f f' = R :=
  blockValue_eq hq hA hR

/-- If one integral is a monomial multiple of another for every `s`, the same
holds for their continuations. -/
theorem blockContinuationFamily_of_integral (hq : 1 < q) [SFinite μ] [SFinite ν]
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ')
    {f₁ f₂ : (coefficientModel π ℓ).toSubmodule} {f₁' f₂' : (coefficientModel σ ℓ').toSubmodule}
    (c : ℂ) (m : ℤ)
    (h : ∀ t, unequalRankIntegralAt j k hr ψ abv μ ν f₂.val f₂'.val t =
      c * spectralPoint q t ^ m * unequalRankIntegralAt j k hr ψ abv μ ν f₁.val f₁'.val t) :
    blockContinuationFamily hq hA f₂ f₂' =
      RatFunc.C c * RatFunc.X ^ m * blockContinuationFamily hq hA f₁ f₁' :=
  blockContinuationFamily_eq hq hA (continuation_of_eq_on_right
    ((blockContinuationFamily_spec hq hA f₁ f₁').monomial_mul (by omega) c m)
    ⟨0, fun t _ => h t⟩)

/-- Every value of the family is cleared by a normalized generator of the
actual rational-value set. -/
theorem blockContinuationFamily_clears (hq : 1 < q) [SFinite μ] [SFinite ν]
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ') {P : Polynomial ℂ}
    (hP : IsNormalizedGenerator (unequalRankValuesAt j k hr q ψ abv μ ν π σ ℓ ℓ') P)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule) :
    ∃ a : LaurentCoefficients, laurentToRatFunc a =
      algebraMap (Polynomial ℂ) RationalFunctions P * blockContinuationFamily hq hA f f' := by
  refine hP.clearsDenominators (mem_zetaSpan ?_)
  rw [unequalRankValuesAt_eq_set]
  exact ⟨f, f', blockContinuationFamily_spec hq hA f f'⟩

theorem UnequalRankAnalyticAt.exists_normalizedGenerator
    (hA : UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ') :
    ∃ P : Polynomial ℂ, IsNormalizedGenerator (unequalRankValuesAt j k hr q ψ abv μ ν π σ ℓ ℓ') P := by
  subst hr
  exact hA.2.2.2

end Family

end Langlands.RankinSelberg
