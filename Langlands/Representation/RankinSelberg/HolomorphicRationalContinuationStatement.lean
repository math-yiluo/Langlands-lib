import Langlands.Representation.RankinSelberg.RationalContinuation
import Langlands.Representation.RankinSelberg.RationalEvaluation
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-!
# Regularity of a rational continuation of a holomorphic function

This internal statement transfers holomorphy on the positive half-plane to
regularity of the rational continuation on the punctured unit disk.
-/

namespace Langlands.RankinSelberg

/-- A function holomorphic on the positive half-plane has no reduced-denominator
poles there in any rational continuation in `q^(-s)`. Equivalently, its rational
continuation is regular on the punctured unit disk. Both conclusions are bundled
for consumers; neither asserts regularity at zero. -/
def HolomorphicRationalContinuationStatement : Prop :=
  ∀ (q : ℕ), 1 < q → ∀ (f : ℂ → ℂ) (R : RatFunc ℂ),
    DifferentiableOn ℂ f {s : ℂ | 0 < s.re} →
    HasRationalContinuation q f R →
    (∀ s : ℂ, 0 < s.re → R.denom.eval (spectralPoint q s) ≠ 0) ∧
    (∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < 1 → RationalEvaluation.RegularAt R z)

end Langlands.RankinSelberg
