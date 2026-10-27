import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.EqualRankUnitNormalization
import Langlands.Representation.RankinSelberg.EqualRankCharacterChange
import Langlands.Representation.RankinSelberg.RationalContinuationLinearProof

/-!
# Linearity, right translation and the trilinear continuation family

The actual equal-rank integrals are additive in each argument where both
summands converge, homogeneous everywhere, and transform under simultaneous
right translation by the determinant weight `|det g|^(-s)`. Under the published
analytic conclusion, their rational continuations form a trilinear map whose
values on translated triples are multiplied by the monomial `X^m`.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open RationalContinuationLinear

universe uF uV uW

section Integrand

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

theorem equalRankIntegrand_add_left (W₁ W₂ : WhittakerFunctions ψ n)
    (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (x : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv (W₁ + W₂) W' Φ s x =
      equalRankIntegrand ψ abv W₁ W' Φ s x + equalRankIntegrand ψ abv W₂ W' Φ s x := by
  induction x using Quotient.inductionOn with
  | h g =>
    simp only [equalRankIntegrand_mk]
    change (W₁.val g + W₂.val g) * W'.val g * Φ (lastRow g) * determinantWeight abv g s = _
    ring

theorem equalRankIntegrand_add_middle (W : WhittakerFunctions ψ n)
    (W'₁ W'₂ : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (x : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv W (W'₁ + W'₂) Φ s x =
      equalRankIntegrand ψ abv W W'₁ Φ s x + equalRankIntegrand ψ abv W W'₂ Φ s x := by
  induction x using Quotient.inductionOn with
  | h g =>
    simp only [equalRankIntegrand_mk]
    change W.val g * (W'₁.val g + W'₂.val g) * Φ (lastRow g) * determinantWeight abv g s = _
    ring

theorem equalRankIntegrand_add_right (W : WhittakerFunctions ψ n)
    (W' : InverseWhittakerFunctions ψ n) (Φ₁ Φ₂ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (x : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv W W' (Φ₁ + Φ₂) s x =
      equalRankIntegrand ψ abv W W' Φ₁ s x + equalRankIntegrand ψ abv W W' Φ₂ s x := by
  induction x using Quotient.inductionOn with
  | h g =>
    simp only [equalRankIntegrand_mk]
    change W.val g * W'.val g * (Φ₁ (lastRow g) + Φ₂ (lastRow g)) *
      determinantWeight abv g s = _
    ring

theorem equalRankIntegrand_smul_middle (c : ℂ) (W : WhittakerFunctions ψ n)
    (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (x : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv W (c • W') Φ s x = c * equalRankIntegrand ψ abv W W' Φ s x := by
  induction x using Quotient.inductionOn with
  | h g =>
    simp only [equalRankIntegrand_mk]
    change W.val g * (c * W'.val g) * Φ (lastRow g) * determinantWeight abv g s = _
    ring

theorem equalRankIntegrand_smul_right (c : ℂ) (W : WhittakerFunctions ψ n)
    (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ)
    (x : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv W W' (c • Φ) s x = c * equalRankIntegrand ψ abv W W' Φ s x := by
  induction x using Quotient.inductionOn with
  | h g =>
    simp only [equalRankIntegrand_mk]
    change W.val g * W'.val g * (c * Φ (lastRow g)) * determinantWeight abv g s = _
    ring

variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))

/-- Additivity in the first function, assuming convergence of both summands only. -/
theorem equalRankIntegral_add_left {W₁ W₂ : WhittakerFunctions ψ n}
    {W' : InverseWhittakerFunctions ψ n} {Φ : SchwartzBruhat (Fin (n + 1) → F)} {s : ℂ}
    (h₁ : EqualRankConverges ψ abv μ W₁ W' Φ s) (h₂ : EqualRankConverges ψ abv μ W₂ W' Φ s) :
    equalRankIntegral ψ abv μ (W₁ + W₂) W' Φ s =
      equalRankIntegral ψ abv μ W₁ W' Φ s + equalRankIntegral ψ abv μ W₂ W' Φ s := by
  simp only [equalRankIntegral, equalRankIntegrand_add_left]
  exact integral_add h₁ h₂

/-- Additivity in the second function, assuming convergence of both summands only. -/
theorem equalRankIntegral_add_middle {W : WhittakerFunctions ψ n}
    {W'₁ W'₂ : InverseWhittakerFunctions ψ n} {Φ : SchwartzBruhat (Fin (n + 1) → F)} {s : ℂ}
    (h₁ : EqualRankConverges ψ abv μ W W'₁ Φ s) (h₂ : EqualRankConverges ψ abv μ W W'₂ Φ s) :
    equalRankIntegral ψ abv μ W (W'₁ + W'₂) Φ s =
      equalRankIntegral ψ abv μ W W'₁ Φ s + equalRankIntegral ψ abv μ W W'₂ Φ s := by
  simp only [equalRankIntegral, equalRankIntegrand_add_middle]
  exact integral_add h₁ h₂

/-- Additivity in the Schwartz--Bruhat function, assuming convergence of both
summands only. -/
theorem equalRankIntegral_add_right {W : WhittakerFunctions ψ n}
    {W' : InverseWhittakerFunctions ψ n} {Φ₁ Φ₂ : SchwartzBruhat (Fin (n + 1) → F)} {s : ℂ}
    (h₁ : EqualRankConverges ψ abv μ W W' Φ₁ s) (h₂ : EqualRankConverges ψ abv μ W W' Φ₂ s) :
    equalRankIntegral ψ abv μ W W' (Φ₁ + Φ₂) s =
      equalRankIntegral ψ abv μ W W' Φ₁ s + equalRankIntegral ψ abv μ W W' Φ₂ s := by
  simp only [equalRankIntegral, equalRankIntegrand_add_right]
  exact integral_add h₁ h₂

theorem equalRankIntegral_smul_middle (c : ℂ) (W : WhittakerFunctions ψ n)
    (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankIntegral ψ abv μ W (c • W') Φ s = c * equalRankIntegral ψ abv μ W W' Φ s := by
  simp only [equalRankIntegral, equalRankIntegrand_smul_middle, integral_const_mul]

theorem equalRankIntegral_smul_right (c : ℂ) (W : WhittakerFunctions ψ n)
    (W' : InverseWhittakerFunctions ψ n) (Φ : SchwartzBruhat (Fin (n + 1) → F)) (s : ℂ) :
    equalRankIntegral ψ abv μ W W' (c • Φ) s = c * equalRankIntegral ψ abv μ W W' Φ s := by
  simp only [equalRankIntegral, equalRankIntegrand_smul_right, integral_const_mul]

end Integrand

section Algebra

variable {F : Type uF} [Field F] {n : ℕ}

/-- The determinant weight at `-s` is an integer power of the spectral point
when `|det g| = q^m`. -/
theorem determinantWeight_neg_eq_spectralPoint_zpow {q : ℕ} (hq : 0 < q)
    (abv : AbsoluteValue F ℝ) {d : ℕ} (g : Langlands.GeneralLinear d F) (m : ℤ)
    (hg : abv (Matrix.det g.val) = (q : ℝ) ^ m) (s : ℂ) :
    determinantWeight abv g (-s) = spectralPoint q s ^ m := by
  rw [determinantWeight_eq_spectralPoint_zpow q hq abv g (-m) (by rw [neg_neg, hg]) (-s)]
  have hinv : spectralPoint q (-s) = (spectralPoint q s)⁻¹ := by
    simp only [spectralPoint, neg_neg, Complex.cpow_neg, inv_inv]
  rw [hinv, inv_zpow', neg_neg]

/-- The determinant weights at `-s` and `s` are inverse to each other. -/
theorem determinantWeight_neg_mul_self (abv : AbsoluteValue F ℝ) {d : ℕ}
    (g : Langlands.GeneralLinear d F) (s : ℂ) :
    determinantWeight abv g (-s) * determinantWeight abv g s = 1 := by
  have h0 := determinantWeight_ne_zero abv g s
  unfold determinantWeight at h0 ⊢
  rw [Complex.cpow_neg, inv_mul_cancel₀ h0]

end Algebra

section Translation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)

/-- Pointwise right translation law of the quotient integrand. -/
theorem equalRankIntegrand_translate (g : Langlands.GeneralLinear (n + 1) F)
    {W Wg : WhittakerFunctions ψ n} {W' W'g : InverseWhittakerFunctions ψ n}
    {Φ Φg : SchwartzBruhat (Fin (n + 1) → F)}
    (hW : ∀ h, Wg.val h = W.val (h * g)) (hW' : ∀ h, W'g.val h = W'.val (h * g))
    (hΦ : ∀ x, Φg x = Φ (Matrix.vecMul x g.val)) (s : ℂ) (x : LeftUnipotentQuotient n F) :
    equalRankIntegrand ψ abv Wg W'g Φg s x =
      determinantWeight abv g (-s) *
        equalRankIntegrand ψ abv W W' Φ s (rightTranslate (upperUnipotent (n + 1) F) g x) := by
  induction x using Quotient.inductionOn with
  | h h =>
    simp only [rightTranslate_mk, equalRankIntegrand_mk]
    rw [hW, hW', hΦ, ← lastRow_mul_eq_vecMul, determinantWeight_mul]
    linear_combination (-(W.val (h * g) * W'.val (h * g) * Φ (lastRow (h * g)) *
      determinantWeight abv h s)) * determinantWeight_neg_mul_self abv g s

variable [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  (μ : Measure (LeftUnipotentQuotient n F))

/-- Simultaneous right translation multiplies the equal-rank integral by
`|det g|^(-s)`, for every complex `s`. -/
theorem equalRankIntegral_translate
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F)
    {W Wg : WhittakerFunctions ψ n} {W' W'g : InverseWhittakerFunctions ψ n}
    {Φ Φg : SchwartzBruhat (Fin (n + 1) → F)}
    (hW : ∀ h, Wg.val h = W.val (h * g)) (hW' : ∀ h, W'g.val h = W'.val (h * g))
    (hΦ : ∀ x, Φg x = Φ (Matrix.vecMul x g.val)) (s : ℂ) :
    equalRankIntegral ψ abv μ Wg W'g Φg s =
      determinantWeight abv g (-s) * equalRankIntegral ψ abv μ W W' Φ s := by
  have he : equalRankIntegrand ψ abv Wg W'g Φg s = fun x => determinantWeight abv g (-s) *
      equalRankIntegrand ψ abv W W' Φ s (rightTranslate (upperUnipotent (n + 1) F) g x) :=
    funext (equalRankIntegrand_translate ψ abv g hW hW' hΦ s)
  unfold equalRankIntegral
  rw [he, integral_const_mul,
    (hμ g).integral_comp (rightTranslate (upperUnipotent (n + 1) F) g).measurableEmbedding]

/-- Simultaneous right translation preserves absolute convergence. -/
theorem equalRankConverges_translate_iff
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F)
    {W Wg : WhittakerFunctions ψ n} {W' W'g : InverseWhittakerFunctions ψ n}
    {Φ Φg : SchwartzBruhat (Fin (n + 1) → F)}
    (hW : ∀ h, Wg.val h = W.val (h * g)) (hW' : ∀ h, W'g.val h = W'.val (h * g))
    (hΦ : ∀ x, Φg x = Φ (Matrix.vecMul x g.val)) (s : ℂ) :
    EqualRankConverges ψ abv μ Wg W'g Φg s ↔ EqualRankConverges ψ abv μ W W' Φ s := by
  have he : equalRankIntegrand ψ abv Wg W'g Φg s = fun x => determinantWeight abv g (-s) *
      equalRankIntegrand ψ abv W W' Φ s (rightTranslate (upperUnipotent (n + 1) F) g x) :=
    funext (equalRankIntegrand_translate ψ abv g hW hW' hΦ s)
  unfold EqualRankConverges
  rw [he, integrable_const_mul_iff (isUnit_iff_ne_zero.mpr (determinantWeight_ne_zero abv g (-s)))]
  exact (hμ g).integrable_comp_emb (rightTranslate (upperUnipotent (n + 1) F) g).measurableEmbedding

end Translation

section Family

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  [MeasurableSpace (LeftUnipotentQuotient n F)]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {q : ℕ} {ψ : UnitaryAdditiveCharacter F} {abv : AbsoluteValue F ℝ}
  {μ : Measure (LeftUnipotentQuotient n F)}
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W}
  {ℓ : glFunctionals ψ n π} {ℓ' : glInverseFunctionals ψ n σ}

/-- The rational continuation chosen for one triple. -/
private def continuationValue (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) : RationalFunctions :=
  Classical.choose (hA.2.1 f f' Φ)

private theorem continuationValue_spec (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ)
      (continuationValue hA f f' Φ) :=
  Classical.choose_spec (hA.2.1 f f' Φ)

private theorem continuationValue_eq (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    {f : (coefficientModel π ℓ).toSubmodule} {f' : (coefficientModel σ ℓ').toSubmodule}
    {Φ : SchwartzBruhat (Fin (n + 1) → F)} {R : RationalFunctions}
    (hR : HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R) :
    continuationValue hA f f' Φ = R :=
  (continuationValue_spec hA f f' Φ).unique hq hR

/-- Constant multiples: the integrals are homogeneous for every `s`. -/
private theorem continuation_smul {c : ℂ} {I J : ℂ → ℂ} {R : RationalFunctions}
    (hR : HasRationalContinuation q I R) (hIJ : ∀ s, J s = c * I s) :
    HasRationalContinuation q J (c • R) := by
  rw [RatFunc.smul_eq_C_mul]
  exact continuation_of_eq_on_right (hasRationalContinuation_const_mul c hR)
    ⟨0, fun s _ => hIJ s⟩

private theorem continuationValue_add_left (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (f₁ f₂ : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    continuationValue hA (f₁ + f₂) f' Φ =
      continuationValue hA f₁ f' Φ + continuationValue hA f₂ f' Φ := by
  obtain ⟨a₁, h₁⟩ := hA.1 f₁ f' Φ
  obtain ⟨a₂, h₂⟩ := hA.1 f₂ f' Φ
  refine continuationValue_eq hq hA (continuation_of_eq_on_right
    (continuation_add (continuationValue_spec hA f₁ f' Φ) (continuationValue_spec hA f₂ f' Φ))
    ⟨max a₁ a₂, fun s hs => ?_⟩)
  exact equalRankIntegral_add_left ψ abv μ (h₁ s ((le_max_left _ _).trans_lt hs))
    (h₂ s ((le_max_right _ _).trans_lt hs))

private theorem continuationValue_add_middle (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f'₁ f'₂ : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    continuationValue hA f (f'₁ + f'₂) Φ =
      continuationValue hA f f'₁ Φ + continuationValue hA f f'₂ Φ := by
  obtain ⟨a₁, h₁⟩ := hA.1 f f'₁ Φ
  obtain ⟨a₂, h₂⟩ := hA.1 f f'₂ Φ
  refine continuationValue_eq hq hA (continuation_of_eq_on_right
    (continuation_add (continuationValue_spec hA f f'₁ Φ) (continuationValue_spec hA f f'₂ Φ))
    ⟨max a₁ a₂, fun s hs => ?_⟩)
  exact equalRankIntegral_add_middle ψ abv μ (h₁ s ((le_max_left _ _).trans_lt hs))
    (h₂ s ((le_max_right _ _).trans_lt hs))

private theorem continuationValue_add_right (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ₁ Φ₂ : SchwartzBruhat (Fin (n + 1) → F)) :
    continuationValue hA f f' (Φ₁ + Φ₂) =
      continuationValue hA f f' Φ₁ + continuationValue hA f f' Φ₂ := by
  obtain ⟨a₁, h₁⟩ := hA.1 f f' Φ₁
  obtain ⟨a₂, h₂⟩ := hA.1 f f' Φ₂
  refine continuationValue_eq hq hA (continuation_of_eq_on_right
    (continuation_add (continuationValue_spec hA f f' Φ₁) (continuationValue_spec hA f f' Φ₂))
    ⟨max a₁ a₂, fun s hs => ?_⟩)
  exact equalRankIntegral_add_right ψ abv μ (h₁ s ((le_max_left _ _).trans_lt hs))
    (h₂ s ((le_max_right _ _).trans_lt hs))

private theorem continuationValue_smul_left (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ') (c : ℂ)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    continuationValue hA (c • f) f' Φ = c • continuationValue hA f f' Φ :=
  continuationValue_eq hq hA (continuation_smul (continuationValue_spec hA f f' Φ)
    fun s => equalRankIntegral_smul_left ψ abv μ c f.val f'.val Φ s)

private theorem continuationValue_smul_middle (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ') (c : ℂ)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    continuationValue hA f (c • f') Φ = c • continuationValue hA f f' Φ :=
  continuationValue_eq hq hA (continuation_smul (continuationValue_spec hA f f' Φ)
    fun s => equalRankIntegral_smul_middle ψ abv μ c f.val f'.val Φ s)

private theorem continuationValue_smul_right (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ') (c : ℂ)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    continuationValue hA f f' (c • Φ) = c • continuationValue hA f f' Φ :=
  continuationValue_eq hq hA (continuation_smul (continuationValue_spec hA f f' Φ)
    fun s => equalRankIntegral_smul_right ψ abv μ c f.val f'.val Φ s)

/-- The trilinear family of rational continuations of the equal-rank model
integrals. Its value at `(f, f', Φ)` is the unique rational continuation. -/
def equalRankContinuationFamily (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ') :
    (coefficientModel π ℓ).toSubmodule →ₗ[ℂ] (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ]
      SchwartzBruhat (Fin (n + 1) → F) →ₗ[ℂ] RationalFunctions where
  toFun f :=
    { toFun := fun f' =>
        { toFun := fun Φ => continuationValue hA f f' Φ
          map_add' := continuationValue_add_right hq hA f f'
          map_smul' := fun c Φ => continuationValue_smul_right hq hA c f f' Φ }
      map_add' := fun f'₁ f'₂ => LinearMap.ext fun Φ =>
        continuationValue_add_middle hq hA f f'₁ f'₂ Φ
      map_smul' := fun c f' => LinearMap.ext fun Φ =>
        continuationValue_smul_middle hq hA c f f' Φ }
  map_add' f₁ f₂ := LinearMap.ext fun f' => LinearMap.ext fun Φ =>
    continuationValue_add_left hq hA f₁ f₂ f' Φ
  map_smul' c f := LinearMap.ext fun f' => LinearMap.ext fun Φ =>
    continuationValue_smul_left hq hA c f f' Φ

theorem equalRankContinuationFamily_spec (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ)
      (equalRankContinuationFamily hq hA f f' Φ) :=
  continuationValue_spec hA f f' Φ

theorem equalRankContinuationFamily_eq (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    {f : (coefficientModel π ℓ).toSubmodule} {f' : (coefficientModel σ ℓ').toSubmodule}
    {Φ : SchwartzBruhat (Fin (n + 1) → F)} {R : RationalFunctions}
    (hR : HasRationalContinuation q (equalRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ) R) :
    equalRankContinuationFamily hq hA f f' Φ = R :=
  continuationValue_eq hq hA hR

/-- Simultaneous right translation multiplies the continuation by `X^m` when
`|det g| = q^m`. -/
theorem equalRankContinuationFamily_translate [IsTopologicalRing F]
    [BorelSpace (LeftUnipotentQuotient n F)] (hq : 1 < q)
    (hA : EqualRankAnalyticConclusion q ψ abv μ π σ ℓ ℓ')
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F) (m : ℤ)
    (hg : abv (Matrix.det g.val) = (q : ℝ) ^ m)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    {Φ Φg : SchwartzBruhat (Fin (n + 1) → F)} (hΦ : ∀ x, Φg x = Φ (Matrix.vecMul x g.val)) :
    equalRankContinuationFamily hq hA (modelRepresentation π ℓ g f)
        (modelRepresentation σ ℓ' g f') Φg =
      RatFunc.X ^ m * equalRankContinuationFamily hq hA f f' Φ := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have h := (equalRankContinuationFamily_spec hq hA f f' Φ).monomial_mul hq0 1 m
  rw [map_one, one_mul] at h
  refine equalRankContinuationFamily_eq hq hA (continuation_of_eq_on_right h ⟨0, fun s _ => ?_⟩)
  change equalRankIntegral ψ abv μ (modelRepresentation π ℓ g f).val
      (modelRepresentation σ ℓ' g f').val Φg s =
    1 * spectralPoint q s ^ m * equalRankIntegral ψ abv μ f.val f'.val Φ s
  rw [equalRankIntegral_translate ψ abv μ hμ g (fun _ => rfl) (fun _ => rfl) hΦ s,
    determinantWeight_neg_eq_spectralPoint_zpow hq0 abv g m hg s, one_mul]
  rfl

end Family

section DualModels

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  (ψ : UnitaryAdditiveCharacter F)

/-- The first dual model map intertwines right translation by `g` with right
translation by the inverse transpose of `g`. -/
theorem firstDualModelMap_modelRepresentation
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V) (ℓ : glFunctionals ψ n π)
    (g : Langlands.GeneralLinear (n + 1) F) (f : (coefficientModel π ℓ).toSubmodule) :
    firstDualModelMap ψ π ℓ (modelRepresentation π ℓ g f) =
      modelRepresentation (inverseTransposePullback π) (firstDualFunctional ψ π ℓ)
        (inverseTranspose (n + 1) F g) (firstDualModelMap ψ π ℓ f) := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change f.val.val ((weylLong (n + 1) F * inverseTranspose (n + 1) F x) * g) =
    f.val.val (weylLong (n + 1) F *
      inverseTranspose (n + 1) F (x * inverseTranspose (n + 1) F g))
  rw [map_mul, inverseTranspose_involutive, mul_assoc]

/-- The second dual model map intertwines right translation by `g` with right
translation by the inverse transpose of `g`. -/
theorem secondDualModelMap_modelRepresentation
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ' : glInverseFunctionals ψ n σ)
    (g : Langlands.GeneralLinear (n + 1) F) (f' : (coefficientModel σ ℓ').toSubmodule) :
    secondDualModelMap ψ σ ℓ' (modelRepresentation σ ℓ' g f') =
      modelRepresentation (inverseTransposePullback σ) (secondDualFunctional ψ σ ℓ')
        (inverseTranspose (n + 1) F g) (secondDualModelMap ψ σ ℓ' f') := by
  apply Subtype.ext
  apply Subtype.ext
  funext x
  change f'.val.val ((weylLong (n + 1) F * inverseTranspose (n + 1) F x) * g) =
    f'.val.val (weylLong (n + 1) F *
      inverseTranspose (n + 1) F (x * inverseTranspose (n + 1) F g))
  rw [map_mul, inverseTranspose_involutive, mul_assoc]

/-- The dual integral is the equal-rank model integral of the transformed
models, for the inverse character. -/
theorem dualEqualRankModelIntegral_eq (abv : AbsoluteValue F ℝ)
    [MeasurableSpace (LeftUnipotentQuotient n F)] (μ : Measure (LeftUnipotentQuotient n F))
    (π : Representation ℂ (Langlands.GeneralLinear (n + 1) F) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F) W)
    (ℓ : glFunctionals ψ n π) (ℓ' : glInverseFunctionals ψ n σ)
    (f : (coefficientModel π ℓ).toSubmodule) (f' : (coefficientModel σ ℓ').toSubmodule)
    (Φ : SchwartzBruhat (Fin (n + 1) → F)) :
    dualEqualRankModelIntegral ψ abv μ π σ ℓ ℓ' f f' Φ =
      equalRankModelIntegral (ψ.scale (-1)) abv μ (inverseTransposePullback π)
        (inverseTransposePullback σ) (firstDualFunctional ψ π ℓ) (secondDualFunctional ψ σ ℓ')
        (firstDualModelMap ψ π ℓ f) (secondDualModelMap ψ σ ℓ' f') Φ := rfl

end DualModels

end Langlands.RankinSelberg
