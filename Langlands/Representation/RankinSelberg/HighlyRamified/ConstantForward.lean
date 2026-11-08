import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.PairFactors

/-!
# A monomial gamma factor and a monomial dual integral give a constant forward integral

If the gamma factor is `C X^N` and, on a right half-plane, the dual integral is
`c_d X^(-N)` (with `X = q^(-s)`), then the functional equation forces the forward integral to be
the constant `(ζ^e)⁻¹ C⁻¹ c_d q^N` on a right half-plane.
-/

noncomputable section

namespace Langlands.RankinSelberg.HighlyRamified

open Polynomial

/-- `q^(-(1-s)) = q⁻¹ / q^(-s)`. -/
theorem spectralPoint_one_sub (q : ℕ) (hq : 0 < q) (s : ℂ) :
    spectralPoint q (1 - s) = (q : ℂ)⁻¹ * (spectralPoint q s)⁻¹ := by
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  unfold spectralPoint
  rw [neg_sub, Complex.cpow_sub _ _ hq0, Complex.cpow_one, Complex.cpow_neg, inv_inv]
  ring

/-- The forward integral is constant when the gamma factor and the dual integral are
monomials of opposite degrees. -/
theorem forward_eq_const_of_monomial {q : ℕ} (hq : 1 < q) {ζ : ℂˣ} {e : ℕ}
    {R Rd : RationalFunctions} {I J : ℂ → ℂ} (C : ℂˣ) (N : ℤ) (cd : ℂˣ)
    (hR : HasRationalContinuation q I R) (hRd : HasRationalContinuation q J Rd)
    (hFE : GammaFunctionalEquation q ζ e (rationalEpsilonMonomial C N : RationalFunctions) R Rd)
    (hJ : ∃ b : ℝ, ∀ s : ℂ, b < s.re → J s = (cd : ℂ) * (spectralPoint q s) ^ (-N)) :
    ∃ a : ℝ, ∀ s : ℂ, a < s.re →
      I s = (((ζ : ℂ) ^ e))⁻¹ * (C : ℂ)⁻¹ * cd * (q : ℂ) ^ N := by
  have hq0 : 0 < q := by omega
  have hsp : ∀ s, spectralPoint q s ≠ 0 := spectralPoint_ne_zero_of_pos hq0
  obtain ⟨b, hb⟩ := hJ
  have hRd' : HasRationalContinuation q J (rationalEpsilonMonomial cd (-N) : RationalFunctions) :=
    ⟨b, fun s hs => ⟨regular_rationalEpsilonMonomial cd (-N) (hsp s), by
      rw [eval_rationalEpsilonMonomial cd (-N) (hsp s), hb s hs]⟩⟩
  have hRdeq : Rd = (rationalEpsilonMonomial cd (-N) : RationalFunctions) := hRd.unique hq hRd'
  obtain ⟨a, ha⟩ := hR
  refine ⟨a, fun s hs => ?_⟩
  obtain ⟨hden, hI⟩ := ha s hs
  have h := hFE s hden (by rw [hRdeq]; exact regular_rationalEpsilonMonomial cd (-N) (hsp _))
    (regular_rationalEpsilonMonomial C N (hsp s))
  rw [hRdeq, eval_rationalEpsilonMonomial cd (-N) (hsp _),
    eval_rationalEpsilonMonomial C N (hsp s), spectralPoint_one_sub q hq0 s] at h
  rw [hI]
  have hq0' : (q : ℂ) ≠ 0 := by exact_mod_cast hq0.ne'
  have hzpow : (((q : ℂ)⁻¹ * (spectralPoint q s)⁻¹) ^ (-N)) =
      (q : ℂ) ^ N * (spectralPoint q s) ^ N := by
    rw [mul_zpow, inv_zpow', inv_zpow', neg_neg]
  rw [hzpow] at h
  have hζ : ((ζ : ℂ) ^ e) ≠ 0 := pow_ne_zero _ ζ.ne_zero
  have hC : (C : ℂ) ≠ 0 := C.ne_zero
  have hX : (spectralPoint q s) ^ N ≠ 0 := zpow_ne_zero _ (hsp s)
  have hne : ((ζ : ℂ) ^ e * C * (spectralPoint q s) ^ N) ≠ 0 := mul_ne_zero (mul_ne_zero hζ hC) hX
  apply mul_left_cancel₀ hne
  rw [show ((ζ : ℂ) ^ e * C * (spectralPoint q s) ^ N) *
      ((((ζ : ℂ) ^ e))⁻¹ * (C : ℂ)⁻¹ * cd * (q : ℂ) ^ N) =
      cd * ((q : ℂ) ^ N * (spectralPoint q s) ^ N) by field_simp]
  linear_combination -h

end Langlands.RankinSelberg.HighlyRamified
