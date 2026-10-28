import Langlands.Representation.RankinSelberg.UnequalRankBlockCoordinates
import Langlands.Representation.RankinSelberg.EqualRankContinuationFamily
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Linearity and covariance laws of the actual unequal-rank integrals

For every block `(j, k)` the actual iterated JPSS integral is additive in each
function where both summands converge absolutely, and homogeneous everywhere.
Under simultaneous right translation by `diag(g, I)` and `g` it is multiplied by
a determinant weight, provided the rectangular measure scales by
`|det g|^(-j)` under `x ↦ x g`. Under a pointwise identity relating the two
first functions along the block matrices through an inner change of variables
`x ↦ φ x` preserving the rectangular measure, it is multiplied by the same scalar.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF

section Integrand

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (j k : ℕ)

theorem unequalRankIntegrand_add_left (W₁ W₂ : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv j k (W₁ + W₂) W' s x q =
      unequalRankIntegrand ψ abv j k W₁ W' s x q + unequalRankIntegrand ψ abv j k W₂ W' s x q := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk]
    change (W₁.val _ + W₂.val _) * W'.val g * _ = _
    ring

theorem unequalRankIntegrand_add_right (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W'₁ W'₂ : InverseWhittakerFunctions ψ n) (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv j k W (W'₁ + W'₂) s x q =
      unequalRankIntegrand ψ abv j k W W'₁ s x q + unequalRankIntegrand ψ abv j k W W'₂ s x q := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk]
    change W.val _ * (W'₁.val g + W'₂.val g) * _ = _
    ring

theorem unequalRankIntegrand_smul_left (c : ℂ) (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv j k (c • W) W' s x q =
      c * unequalRankIntegrand ψ abv j k W W' s x q := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk]
    change (c * W.val _) * W'.val g * _ = _
    ring

theorem unequalRankIntegrand_smul_right (c : ℂ) (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv j k W (c • W') s x q =
      c * unequalRankIntegrand ψ abv j k W W' s x q := by
  induction q using Quotient.inductionOn with
  | h g =>
    simp only [unequalRankIntegrand_mk]
    change W.val _ * (c * W'.val g) * _ = _
    ring

variable [MeasurableSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  (μ : Measure (LeftUnipotentQuotient n F)) (ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F))

/-- Additivity in the first function, assuming absolute convergence of both
summands only. -/
theorem unequalRankIntegral_add_left [SFinite μ] [SFinite ρ]
    {W₁ W₂ : WhittakerFunctions ψ (n + (j + k + 1))} {W' : InverseWhittakerFunctions ψ n}
    {s : ℂ} (h₁ : UnequalRankConverges ψ abv j k μ ρ W₁ W' s)
    (h₂ : UnequalRankConverges ψ abv j k μ ρ W₂ W' s) :
    unequalRankIntegral ψ abv j k μ ρ (W₁ + W₂) W' s =
      unequalRankIntegral ψ abv j k μ ρ W₁ W' s + unequalRankIntegral ψ abv j k μ ρ W₂ W' s := by
  simp only [unequalRankIntegral, unequalRankIntegrand_add_left]
  exact integral_integral_add h₁ h₂

/-- Additivity in the second function, assuming absolute convergence of both
summands only. -/
theorem unequalRankIntegral_add_right [SFinite μ] [SFinite ρ]
    {W : WhittakerFunctions ψ (n + (j + k + 1))} {W'₁ W'₂ : InverseWhittakerFunctions ψ n}
    {s : ℂ} (h₁ : UnequalRankConverges ψ abv j k μ ρ W W'₁ s)
    (h₂ : UnequalRankConverges ψ abv j k μ ρ W W'₂ s) :
    unequalRankIntegral ψ abv j k μ ρ W (W'₁ + W'₂) s =
      unequalRankIntegral ψ abv j k μ ρ W W'₁ s + unequalRankIntegral ψ abv j k μ ρ W W'₂ s := by
  simp only [unequalRankIntegral, unequalRankIntegrand_add_right]
  exact integral_integral_add h₁ h₂

theorem unequalRankIntegral_smul_left (c : ℂ) (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv j k μ ρ (c • W) W' s =
      c * unequalRankIntegral ψ abv j k μ ρ W W' s := by
  simp only [unequalRankIntegral, unequalRankIntegrand_smul_left, integral_const_mul]

theorem unequalRankIntegral_smul_right (c : ℂ) (W : WhittakerFunctions ψ (n + (j + k + 1)))
    (W' : InverseWhittakerFunctions ψ n) (s : ℂ) :
    unequalRankIntegral ψ abv j k μ ρ W (c • W') s =
      c * unequalRankIntegral ψ abv j k μ ρ W W' s := by
  simp only [unequalRankIntegral, unequalRankIntegrand_smul_right, integral_const_mul]

/-- An inner change of variables: if the first functions are related along the
block matrices through `x ↦ φ x`, and `φ` preserves integrals against the
rectangular measure, the integrals differ by the same scalar for every `s`. -/
theorem unequalRankIntegral_of_inner_change
    {W₁ W₂ : WhittakerFunctions ψ (n + (j + k + 1))} {W' : InverseWhittakerFunctions ψ n}
    (φ : Matrix (Fin j) (Fin (n + 1)) F → Matrix (Fin j) (Fin (n + 1)) F) (c : ℂ)
    (hW : ∀ (g : Langlands.GeneralLinear (n + 1) F) (x : Matrix (Fin j) (Fin (n + 1)) F),
      W₂.val (unequalRankMatrix j k g x) = c * W₁.val (unequalRankMatrix j k g (φ x)))
    (hρ : ∀ G : Matrix (Fin j) (Fin (n + 1)) F → ℂ, ∫ x, G (φ x) ∂ρ = ∫ x, G x ∂ρ) (s : ℂ) :
    unequalRankIntegral ψ abv j k μ ρ W₂ W' s = c * unequalRankIntegral ψ abv j k μ ρ W₁ W' s := by
  have he : ∀ x q, unequalRankIntegrand ψ abv j k W₂ W' s x q =
      c * unequalRankIntegrand ψ abv j k W₁ W' s (φ x) q := by
    intro x q
    induction q using Quotient.inductionOn with
    | h g =>
      simp only [unequalRankIntegrand_mk]
      rw [hW]
      ring
  unfold unequalRankIntegral
  simp only [he, integral_const_mul]
  congr 1
  congr 1
  funext q
  exact hρ (fun x => unequalRankIntegrand ψ abv j k W₁ W' s x q)

end Integrand

section Translation

variable {F : Type uF} [Field F] [TopologicalSpace F] [IsTopologicalRing F] {n : ℕ}
  (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ) (j k : ℕ)

omit [TopologicalSpace F] [IsTopologicalRing F] in
/-- The determinant weight is additive in its complex exponent. -/
theorem determinantWeight_exponent_add {d : ℕ} (g : Langlands.GeneralLinear d F) (s t : ℂ) :
    determinantWeight abv g (s + t) = determinantWeight abv g s * determinantWeight abv g t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr (abv.ne_zero (determinant g).ne_zero))

/-- Pointwise right translation law of the unequal-rank integrand. -/
theorem unequalRankIntegrand_translate (g : Langlands.GeneralLinear (n + 1) F)
    {W₁ W₂ : WhittakerFunctions ψ (n + (j + k + 1))} {W₁' W₂' : InverseWhittakerFunctions ψ n}
    (hW : ∀ h, W₂.val h = W₁.val (h * appendIdentity n (j + k + 1) g))
    (hW' : ∀ h, W₂'.val h = W₁'.val (h * g)) (s : ℂ) (x : Matrix (Fin j) (Fin (n + 1)) F)
    (q : LeftUnipotentQuotient n F) :
    unequalRankIntegrand ψ abv j k W₂ W₂' s x q =
      determinantWeight abv g (((j + k + 1 : ℕ) : ℂ) / 2 - s) *
        unequalRankIntegrand ψ abv j k W₁ W₁' s (x * g.val)
          (rightTranslate (upperUnipotent (n + 1) F) g q) := by
  induction q using Quotient.inductionOn with
  | h h =>
    simp only [rightTranslate_mk, unequalRankIntegrand_mk]
    rw [hW, hW', unequalRankMatrix_mul_appendIdentity, determinantWeight_mul]
    have h1 := determinantWeight_neg_mul_self abv g (s - ((j + k + 1 : ℕ) : ℂ) / 2)
    rw [neg_sub] at h1
    linear_combination (-(W₁.val (unequalRankMatrix j k (h * g) (x * g.val)) *
      W₁'.val (h * g) * determinantWeight abv h (s - ((j + k + 1 : ℕ) : ℂ) / 2))) * h1

variable [MeasurableSpace (LeftUnipotentQuotient n F)] [BorelSpace (LeftUnipotentQuotient n F)]
  [MeasurableSpace (Matrix (Fin j) (Fin (n + 1)) F)]
  (μ : Measure (LeftUnipotentQuotient n F)) (ρ : Measure (Matrix (Fin j) (Fin (n + 1)) F))

/-- Simultaneous right translation by `diag(g, I)` and `g` multiplies the
unequal-rank integral by `|det g|^((j+k+1)/2 - s - j)`, for every complex `s`,
when the quotient measure is right invariant and the rectangular measure
scales by `|det g|^(-j)` under `x ↦ x g`. -/
theorem unequalRankIntegral_translate
    (hμ : ∀ g, MeasurePreserving (rightTranslate (upperUnipotent (n + 1) F) g) μ μ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (hρ : ∀ G : Matrix (Fin j) (Fin (n + 1)) F → ℂ,
      ∫ x, G (x * g.val) ∂ρ = determinantWeight abv g (-(j : ℂ)) * ∫ x, G x ∂ρ)
    {W₁ W₂ : WhittakerFunctions ψ (n + (j + k + 1))} {W₁' W₂' : InverseWhittakerFunctions ψ n}
    (hW : ∀ h, W₂.val h = W₁.val (h * appendIdentity n (j + k + 1) g))
    (hW' : ∀ h, W₂'.val h = W₁'.val (h * g)) (s : ℂ) :
    unequalRankIntegral ψ abv j k μ ρ W₂ W₂' s =
      determinantWeight abv g (((j + k + 1 : ℕ) : ℂ) / 2 - s - j) *
        unequalRankIntegral ψ abv j k μ ρ W₁ W₁' s := by
  unfold unequalRankIntegral
  simp only [unequalRankIntegrand_translate ψ abv j k g hW hW' s, integral_const_mul]
  have hinner : ∀ q, ∫ x, unequalRankIntegrand ψ abv j k W₁ W₁' s (x * g.val)
      (rightTranslate (upperUnipotent (n + 1) F) g q) ∂ρ =
      determinantWeight abv g (-(j : ℂ)) * ∫ x, unequalRankIntegrand ψ abv j k W₁ W₁' s x
        (rightTranslate (upperUnipotent (n + 1) F) g q) ∂ρ :=
    fun q => hρ (fun x => unequalRankIntegrand ψ abv j k W₁ W₁' s x
      (rightTranslate (upperUnipotent (n + 1) F) g q))
  simp only [hinner, integral_const_mul]
  rw [(hμ g).integral_comp (rightTranslate (upperUnipotent (n + 1) F) g).measurableEmbedding
      (fun q => ∫ x, unequalRankIntegrand ψ abv j k W₁ W₁' s x q ∂ρ),
    sub_eq_add_neg _ (j : ℂ), determinantWeight_exponent_add, mul_assoc]

end Translation

end Langlands.RankinSelberg
