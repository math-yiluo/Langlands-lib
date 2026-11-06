import Langlands.LocalFactor.Euler.Definitions
import Langlands.Representation.Unitary.Basic

/-!
# Regularity of Euler denominators for unitary operators

A preserved positive Hermitian form forces every zero of the determinant Euler
polynomial onto the unit circle.
-/

noncomputable section

namespace Langlands.LocalFactor

universe uV

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  [FiniteDimensional ℂ V]

/-- A positive-form-preserving operator has no Euler zeros off the unit circle. -/
theorem eulerPolynomial_eval_ne_zero_of_preserves_positive_form
    (A : Module.End ℂ V) (h : InnerProductSpace.Core ℂ V)
    (hA : ∀ v w, h.inner (A v) (A w) = h.inner v w)
    {z : ℂ} (hz : ‖z‖ ≠ 1) : (eulerPolynomial A).eval z ≠ 0 := by
  let := h
  rw [eulerPolynomial_eval]
  intro hd
  obtain ⟨v, hvker, hvne⟩ :=
    (LinearMap.ker (1 - z • A)).ne_bot_iff.mp
      (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hd)
  have hv : v = z • A v := by
    exact sub_eq_zero.mp (show v - z • A v = 0 from hvker)
  have hi : h.inner v v ≠ 0 := fun h0 => hvne (h.definite v h0)
  have hscale : h.inner v v = (‖z‖ ^ 2 : ℂ) * h.inner v v := by
    calc
      h.inner v v = h.inner (z • A v) (z • A v) := congrArg₂ h.inner hv hv
      _ = (‖z‖ ^ 2 : ℂ) * h.inner v v := by
        rw [h.smul_left, InnerProductSpace.Core.inner_smul_right, ← mul_assoc,
          Complex.conj_mul', hA]
  have hs : (1 : ℂ) = (‖z‖ ^ 2 : ℂ) := by
    apply mul_right_cancel₀ hi
    simpa only [one_mul] using hscale
  have hs' : (1 : ℝ) = ‖z‖ ^ 2 := by exact_mod_cast hs
  apply hz
  nlinarith [norm_nonneg z]

/-- A point off the unit circle belongs to the actual Euler regular domain. -/
def regularPointOfPreservesPositiveForm
    (A : Module.End ℂ V) (h : InnerProductSpace.Core ℂ V)
    (hA : ∀ v w, h.inner (A v) (A w) = h.inner v w)
    (z : ℂ) (hz : ‖z‖ ≠ 1) : RegularPoint A :=
  ⟨z, eulerPolynomial_eval_ne_zero_of_preserves_positive_form A h hA hz⟩

/-- The norm of the actual exponential spectral parameter. -/
theorem norm_spectralParameter (q : ℝ) (hq : 0 < q) (s : ℂ) :
    ‖(spectralParameter q hq s : ℂ)‖ = Real.exp (-s.re * Real.log q) := by
  simp [spectralParameter, Complex.norm_exp, Complex.mul_re]

/-- For a residue cardinality greater than one, a nonzero real part gives a
spectral parameter off the unit circle. -/
theorem norm_spectralParameter_ne_one {q : ℝ} (hq : 1 < q)
    {s : ℂ} (hs : s.re ≠ 0) :
    ‖(spectralParameter q (lt_trans zero_lt_one hq) s : ℂ)‖ ≠ 1 := by
  rw [norm_spectralParameter, ne_eq, Real.exp_eq_one_iff]
  exact mul_ne_zero (neg_ne_zero.mpr hs) (Real.log_pos hq).ne'

/-- The Euler denominator is nonzero away from the imaginary spectral axis. -/
theorem eulerPolynomial_spectral_eval_ne_zero_of_preserves_positive_form
    (A : Module.End ℂ V) (h : InnerProductSpace.Core ℂ V)
    (hA : ∀ v w, h.inner (A v) (A w) = h.inner v w)
    {q : ℝ} (hq : 1 < q) {s : ℂ} (hs : s.re ≠ 0) :
    (eulerPolynomial A).eval
      (spectralParameter q (lt_trans zero_lt_one hq) s : ℂ) ≠ 0 :=
  eulerPolynomial_eval_ne_zero_of_preserves_positive_form A h hA
    (norm_spectralParameter_ne_one hq hs)

/-- Construct a point of the genuine spectral regular domain from a preserved
positive form, a residue cardinality greater than one and a nonzero real part. -/
def spectralRegularPointOfPreservesPositiveForm
    (A : Module.End ℂ V) (h : InnerProductSpace.Core ℂ V)
    (hA : ∀ v w, h.inner (A v) (A w) = h.inner v w)
    (q : ℝ) (hq : 1 < q) (s : ℂ) (hs : s.re ≠ 0) :
    SpectralRegularPoint A q (lt_trans zero_lt_one hq) :=
  ⟨s, eulerPolynomial_spectral_eval_ne_zero_of_preserves_positive_form A h hA hq hs⟩

end Langlands.LocalFactor
