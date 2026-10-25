import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# Scalar normalization of actual equal-rank test vectors

These elementary identities turn a supplied nonzero constant actual integral
into rational value one. The construction of such test data remains separate.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker

universe uF uV uW

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}

/-- Scaling the first Whittaker function scales the actual quotient integrand. -/
theorem equalRankIntegrand_smul_left (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (c : ℂ)
    (f : WhittakerFunctions ψ n) (f' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (x : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv (c • f) f' Φ s x =
      c * equalRankIntegrand ψ abv f f' Φ s x := by
  induction x using Quotient.inductionOn with
  | h g =>
    simp only [equalRankIntegrand_mk]
    change (c * f.val g) * f'.val g * Φ (lastRow g) * determinantWeight abv g s =
      c * (f.val g * f'.val g * Φ (lastRow g) * determinantWeight abv g s)
    simp only [mul_assoc]

variable [MeasurableSpace (LeftUnipotentQuotient n F)]

/-- The scalar identity holds for the total Bochner integral. -/
theorem equalRankIntegral_smul_left (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F)) (c : ℂ)
    (f : WhittakerFunctions ψ n) (f' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankIntegral ψ abv μ (c • f) f' Φ s =
      c * equalRankIntegral ψ abv μ f f' Φ s := by
  simp only [equalRankIntegral, equalRankIntegrand_smul_left, integral_const_mul]

/-- Scalar multiplication also preserves actual absolute convergence. -/
theorem EqualRankConverges.smul_left (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F)) (c : ℂ)
    (f : WhittakerFunctions ψ n) (f' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (h : EqualRankConverges ψ abv μ f f' Φ s) :
    EqualRankConverges ψ abv μ (c • f) f' Φ s := by
  have he : equalRankIntegrand ψ abv (c • f) f' Φ s =
      fun x => c * equalRankIntegrand ψ abv f f' Φ s x :=
    funext (equalRankIntegrand_smul_left ψ abv c f f' Φ s)
  change Integrable _ μ
  rw [he]
  exact h.const_mul c

section CoefficientModels

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

variable (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)

/-- Divide an actual first coefficient-model vector by a supplied complex scalar.
Membership in the actual coefficient image is preserved by its module structure.
The useful normalization identities require that the scalar be nonzero. -/
def normalizeEqualRankFirstVector (c : ℂ) (f : (coefficientModel π ℓ).toSubmodule) :
    (coefficientModel π ℓ).toSubmodule :=
  c⁻¹ • f

/-- On coefficient images, the integral scales by the same complex scalar. -/
theorem equalRankModelIntegral_smul_left (c : ℂ)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankModelIntegral ψ abv μ π σ ℓ ℓ' (c • f) f' Φ s =
      c * equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ s := by
  exact equalRankIntegral_smul_left ψ abv μ c f.val f'.val Φ s

/-- Dividing the first actual coefficient vector by a nonzero integral value
makes the integral equal to one at that spectral parameter. -/
theorem normalizeEqualRankFirstVector_integral (c : ℂ) (hc : c ≠ 0)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (h : equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ s = c) :
    equalRankModelIntegral ψ abv μ π σ ℓ ℓ'
      (normalizeEqualRankFirstVector ψ π ℓ c f) f' Φ s = 1 := by
  rw [normalizeEqualRankFirstVector, equalRankModelIntegral_smul_left, h,
    inv_mul_cancel₀ hc]

end CoefficientModels

/-- An actual function equal to one on a right half-plane has rational
continuation one, with the required denominator nonvanishing. -/
theorem hasRationalContinuation_one_of_eq_on_halfPlane {q : ℕ} {f : ℂ → ℂ}
    (a : ℝ) (hf : ∀ s : ℂ, a < s.re → f s = 1) :
    HasRationalContinuation q f 1 := by
  refine ⟨a, ?_⟩
  intro s hs
  constructor
  · simp
  · simpa using hf s hs

section RationalValues

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

variable (q : ℕ) (ψ : UnitaryAdditiveCharacter F)
    (abv : AbsoluteValue F ℝ) (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)

/-- A concrete constant-one actual integral gives literal membership in the
existing rational-value set. -/
theorem one_mem_equalRankRationalValues_of_integral_one
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (a : ℝ)
    (h : ∀ s : ℂ, a < s.re →
      equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ s = 1) :
    (1 : RationalFunctions) ∈ equalRankRationalValues q ψ abv μ π σ ℓ ℓ' :=
  ⟨f, f', Φ, hasRationalContinuation_one_of_eq_on_halfPlane a h⟩

/-- A concrete nonzero constant actual integral can be normalized inside the
first actual coefficient image to give rational value one. -/
theorem one_mem_equalRankRationalValues_of_nonzero_constant
    (c : ℂ) (hc : c ≠ 0)
    (f : (coefficientModel π ℓ).toSubmodule)
    (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) (a : ℝ)
    (h : ∀ s : ℂ, a < s.re →
      equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ s = c) :
    (1 : RationalFunctions) ∈ equalRankRationalValues q ψ abv μ π σ ℓ ℓ' := by
  apply one_mem_equalRankRationalValues_of_integral_one q ψ abv μ π σ ℓ ℓ'
    (normalizeEqualRankFirstVector ψ π ℓ c f) f' Φ a
  intro s hs
  exact normalizeEqualRankFirstVector_integral ψ abv μ π σ ℓ ℓ'
    c hc f f' Φ s (h s hs)

end RationalValues

end Langlands.RankinSelberg
