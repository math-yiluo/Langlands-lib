import Mathlib.Basic.Complex.Basic
import Mathlib.RingTheory.PowerSeries.Derivative

/-!
An internal formal-series helper for determinant-polynomial trace comparisons.
This definition alone asserts no matrix identity or automorphic theorem.
-/

namespace Langlands.Automorphic.Unramified

/-- The total formal series `-X * P' * P⁻¹` attached to a complex polynomial.
Intended uniqueness and product consumers require `P.coeff 0 = 1`. -/
noncomputable def polynomialTraceSeries (P : Polynomial ℂ) : PowerSeries ℂ :=
  -PowerSeries.X * PowerSeries.derivative (P : PowerSeries ℂ) *
    (P : PowerSeries ℂ)⁻¹

end Langlands.Automorphic.Unramified
