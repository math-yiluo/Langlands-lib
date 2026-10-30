import Langlands.Representation.RankinSelberg.QuotientIntegrals
import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.RationalZeta
import Langlands.Representation.Whittaker.Iwasawa

/-!
# The reduced value set of the positive-rank rank-one comparison

For `σ` on `GL_(m+2)` and a specified standard functional `ℓ`, the rational
functions continuing the `GL₁` integrals
`∫ W(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2) dg` of model functions `W` of `ℓ`
that converge absolutely on a right half-plane. Both sides of the positive-rank
branch of `RankOneMatrixWhittakerComparisonStatement` are identified with this
set. This module only makes definitions.
-/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV

variable {F : Type uF} [Field F] [TopologicalSpace F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- The embedding `g ↦ diag(det g, 1, …, 1)` of `GL₁` into `GL_(m+2)`. -/
def rankOneEmbedding (m : ℕ) (g : Langlands.GeneralLinear (0 + 1) F) :
    Langlands.GeneralLinear (m + 1 + 1) F :=
  Iwasawa.diagonalUnits (Fin.cons (Matrix.GeneralLinearGroup.det g) 1)

/-- The `GL₁` integrand `W(diag(det g, 1, …, 1)) |det g|^(s - (m+1)/2)` of a model
function of `ℓ`. -/
def rankOneModelIntegrand (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    {m : ℕ} (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)
    (ℓ : glFunctionals ψ (m + 1) σ) (w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule)
    (s : ℂ) (g : Langlands.GeneralLinear (0 + 1) F) : ℂ :=
  glModelFunction ψ (m + 1) σ ℓ w (rankOneEmbedding m g) *
    determinantWeight abv g (s - ((m + 1 : ℕ) : ℂ) / 2)

/-- Rational functions continuing a `GL₁` model integral that converges absolutely
on a right half-plane, for the explicit measure `μ₁` on `GL₁`. -/
def rankOneModelValues (q : ℕ) (ψ : UnitaryAdditiveCharacter F) (abv : AbsoluteValue F ℝ)
    [MeasurableSpace (Langlands.GeneralLinear (0 + 1) F)]
    (μ₁ : Measure (Langlands.GeneralLinear (0 + 1) F)) {m : ℕ}
    (σ : Representation ℂ (Langlands.GeneralLinear (m + 1 + 1) F) V)
    (ℓ : glFunctionals ψ (m + 1) σ) : Set RationalFunctions :=
  {R | ∃ w : (glCoefficientModel ψ (m + 1) σ ℓ).toSubmodule,
    (∃ a : ℝ, ∀ s : ℂ, a < s.re → Integrable (rankOneModelIntegrand ψ abv σ ℓ w s) μ₁) ∧
      HasRationalContinuation q (fun s => ∫ g, rankOneModelIntegrand ψ abv σ ℓ w s g ∂μ₁) R}

end Langlands.RankinSelberg
