import Langlands.Representation.RankinSelberg.GammaFactor
import Langlands.Representation.RankinSelberg.SpectralRescaling

/-! # Opposite spectral shifts in the gamma functional equation -/

noncomputable section

namespace Langlands.RankinSelberg

/-- The exact denominator condition at a translated spectral parameter. -/
theorem spectralRescale_denom_ne_zero_iff {q : ℕ} (hq : 1 < q)
    (u : ℂ) (R : RationalFunctions) (s : ℂ) :
    (rationalRescale (spectralShiftUnit q hq u) R).denom.eval
        (spectralPoint q s) ≠ 0 ↔
      R.denom.eval (spectralPoint q (s + u)) ≠ 0 := by
  simpa only [coe_spectralShiftUnit, ← spectralPoint_add hq] using
    rationalRescale_denom_ne_zero_iff (spectralShiftUnit q hq u) R (spectralPoint q s)

/-- Rational evaluation at a translated spectral parameter. -/
theorem spectralRescale_eval {q : ℕ} (hq : 1 < q)
    (u : ℂ) (R : RationalFunctions) (s : ℂ)
    (h : R.denom.eval (spectralPoint q (s + u)) ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) (spectralPoint q s)
        (rationalRescale (spectralShiftUnit q hq u) R) =
      RatFunc.eval (RingHom.id ℂ) (spectralPoint q (s + u)) R := by
  simpa only [coe_spectralShiftUnit, ← spectralPoint_add hq] using
    rationalRescale_eval (spectralShiftUnit q hq u) R (spectralPoint q s)
      (by simpa only [coe_spectralShiftUnit, ← spectralPoint_add hq] using h)

/-- Translating the forward continuation by `u` and the dual continuation by
`-u` transports the complete scalar gamma equation by the same substitution as
the forward continuation. The reflection is `1 - (s + u)`. -/
theorem GammaFunctionalEquation.shift {q : ℕ} (hq : 1 < q)
    {ζ : ℂˣ} {e : ℕ} {G R Rdual : RationalFunctions}
    (h : GammaFunctionalEquation q ζ e G R Rdual) (u : ℂ) :
    GammaFunctionalEquation q ζ e
      (rationalRescale (spectralShiftUnit q hq u) G)
      (rationalRescale (spectralShiftUnit q hq u) R)
      (rationalRescale (spectralShiftUnit q hq (-u)) Rdual) := by
  intro s hR hD hG
  have hR' := (spectralRescale_denom_ne_zero_iff hq u R s).mp hR
  have hD' := (spectralRescale_denom_ne_zero_iff hq (-u) Rdual (1 - s)).mp hD
  have hG' := (spectralRescale_denom_ne_zero_iff hq u G s).mp hG
  have hreflect : 1 - s + -u = 1 - (s + u) := by ring
  rw [spectralRescale_eval hq u G s hG',
    spectralRescale_eval hq u R s hR',
    spectralRescale_eval hq (-u) Rdual (1 - s) hD', hreflect]
  exact h (s + u) hR' (by simpa only [hreflect] using hD') hG'

end Langlands.RankinSelberg
