import Langlands.LocalFactor.RegularEvaluation.Definitions
import Langlands.LocalFactor.Euler.Definitions
import Langlands.LocalFactor.Analytic.ReciprocalEntire
import Langlands.LocalFactor.Abelian.Padic
import Mathlib.Logic.Equiv.Basic

/-! Callable adapters. All existing specialized definitions remain unchanged. -/

noncomputable section

namespace Langlands.LocalFactor

universe u v

section Euler

variable {K : Type u} [Field K]
variable {V : Type v} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- Euler's polynomial regular points are the common denominator support. -/
def regularEvaluationEquiv (A : Module.End K V) :
    RegularPoint A ≃ RegularEvaluation.Point (eulerPolynomial A).eval :=
  Equiv.refl _

end Euler

section SpectralEuler

variable {V : Type v} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The same spectral input, with its nonvanishing condition made generic. -/
def spectralRegularEvaluationEquiv (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q) :
    SpectralRegularPoint A q hq ≃ RegularEvaluation.Point
      ((eulerPolynomial A).eval ∘ fun s => (spectralParameter q hq s : ℂ)) :=
  Equiv.refl _

/-- Spectral substitution is a map to polynomial inputs, not an equivalence. -/
def spectralToPolynomialPoint (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q)
    (s : SpectralRegularPoint A q hq) :
    RegularEvaluation.Point (eulerPolynomial A).eval :=
  RegularEvaluation.mapInput (eulerPolynomial A).eval
    (fun s => (spectralParameter q hq s : ℂ)) (spectralRegularEvaluationEquiv A q hq s)

end SpectralEuler

namespace ReciprocalEntire

/-- Forget analytic structure only for the purpose of regular numerical evaluation.
The entire function, punctured germs, and poles remain in the original object. -/
def regularEvaluationEquiv (F : ReciprocalEntire) :
    F.RegularPoint ≃ RegularEvaluation.Point F.denominator :=
  Equiv.refl _

end ReciprocalEntire

namespace PadicAbelian

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "MultiplicativeCharacter" =>
  @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology

/-- At the actual conductor, the published predicate is equivalent to the
support of the polynomial evaluated in the spectral variable. -/
def regularEvaluationEquiv (χ : MultiplicativeCharacter) :
    {s : ℂ // RegularPoint T (uniformizerUnit T) χ (T.multiplicativeConductor χ) s} ≃
      RegularEvaluation.Point ((lPolynomial T χ).eval ∘ spectralVariable T) :=
  Equiv.subtypeEquivRight (regularPoint_iff_polynomial_ne_zero T χ)

/-- Send a regular spectral input to the actual polynomial evaluation input. -/
def regularToPolynomialPoint (χ : MultiplicativeCharacter)
    (s : {s : ℂ // RegularPoint T (uniformizerUnit T) χ (T.multiplicativeConductor χ) s}) :
    RegularEvaluation.Point (lPolynomial T χ).eval :=
  RegularEvaluation.mapInput (lPolynomial T χ).eval (spectralVariable T)
    (regularEvaluationEquiv T χ s)

end PadicAbelian
end Langlands.LocalFactor
