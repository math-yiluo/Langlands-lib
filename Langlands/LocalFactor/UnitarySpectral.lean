import Langlands.LocalFactor.UnitaryEuler
import Langlands.LocalFactor.Analytic.ReciprocalEntire
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Meromorphic.Order

/-! # Meromorphic spectral reciprocals of positive-form-preserving operators -/

noncomputable section

open Filter
open scoped Topology

namespace Langlands.LocalFactor

universe uV

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- The actual determinant Euler denominator evaluated at `q^(-s)`. -/
def spectralDenominator (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q) : ℂ → ℂ :=
  fun s => (eulerPolynomial A).eval (spectralParameter q hq s : ℂ)

theorem analyticAt_spectralDenominator
    (A : Module.End ℂ V) (q : ℝ) (hq : 0 < q) (s : ℂ) :
    AnalyticAt ℂ (spectralDenominator A q hq) s := by
  have he : AnalyticAt ℂ
      (fun s : ℂ => Complex.exp (-s * (Real.log q : ℂ))) s :=
    (analyticAt_id.neg.mul analyticAt_const).cexp
  change AnalyticAt ℂ
    (fun z : ℂ => (eulerPolynomial A).eval (Complex.exp (-z * (Real.log q : ℂ)))) s
  simpa [Polynomial.aeval_def] using
    he.aeval_polynomial (eulerPolynomial A)

/-- The reciprocal retains all punctured germs at the original Euler zeros. -/
def spectralReciprocalOfPreservesPositiveForm
    (A : Module.End ℂ V) (h : InnerProductSpace.Core ℂ V)
    (hA : ∀ v w, h.inner (A v) (A w) = h.inner v w)
    (q : ℝ) (hq : 1 < q) : ReciprocalEntire where
  denominator := spectralDenominator A q (lt_trans zero_lt_one hq)
  entire := fun s => (analyticAt_spectralDenominator A q _ s).differentiableAt
  nonzero := ⟨1, eulerPolynomial_spectral_eval_ne_zero_of_preserves_positive_form
    A h hA hq (by simp)⟩

theorem spectralDenominator_eventually_ne_zero
    (A : Module.End ℂ V) (h : InnerProductSpace.Core ℂ V)
    (hA : ∀ v w, h.inner (A v) (A w) = h.inner v w)
    (q : ℝ) (hq : 1 < q) (s : ℂ) :
    ∀ᶠ z in 𝓝[≠] s, spectralDenominator A q (lt_trans zero_lt_one hq) z ≠ 0 :=
  (spectralReciprocalOfPreservesPositiveForm A h hA q hq).denominator_eventually_ne_zero s

theorem spectralReciprocal_order_nonpos
    (A : Module.End ℂ V) (h : InnerProductSpace.Core ℂ V)
    (hA : ∀ v w, h.inner (A v) (A w) = h.inner v w)
    (q : ℝ) (hq : 1 < q) (s : ℂ) :
    meromorphicOrderAt
      (fun z => (spectralDenominator A q (lt_trans zero_lt_one hq) z)⁻¹) s ≤ 0 := by
  have ha := analyticAt_spectralDenominator A q (lt_trans zero_lt_one hq) s
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero ha.meromorphicAt).mpr
    (spectralDenominator_eventually_ne_zero A h hA q hq s)
  change meromorphicOrderAt
    (spectralDenominator A q (lt_trans zero_lt_one hq))⁻¹ s ≤ 0
  rw [meromorphicOrderAt_inv]
  have hp := ha.meromorphicOrderAt_nonneg
  lift meromorphicOrderAt (spectralDenominator A q (lt_trans zero_lt_one hq)) s
    to ℤ using hn with n hn
  exact_mod_cast neg_nonpos.mpr (show (0 : ℤ) ≤ n by exact_mod_cast hp)

end Langlands.LocalFactor
