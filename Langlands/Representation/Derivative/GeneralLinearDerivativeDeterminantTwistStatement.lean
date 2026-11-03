import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Classification.SupercuspidalTwist

/-!
# Determinant twists and general-linear derivatives

The actual Bernstein–Zelevinsky derivative functor commutes, up to a natural
isomorphism, with the real determinant-power twist. The exponent is unchanged
on the smaller general-linear group. This module only defines the proposition.
-/

namespace Langlands.Derivative

open CategoryTheory GeneralLinear HarmonicAnalysis

/-- Natural commutation of every feasible actual general-linear derivative with
every real determinant-power twist, including order zero and residual rank zero. -/
def GeneralLinearDerivativeDeterminantTwistStatement.{uF, uV}
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N k : ℕ) (hk : k ≤ N) (s : ℝ),
    Nonempty
      ((SmoothRep.twistFunctor (T.determinantPowerCharacter N s)
          (T.isOpen_ker_determinantPowerCharacter N s) ⋙
        generalLinearDerivative.{uF, uV} T ψ N k hk) ≅
       (generalLinearDerivative.{uF, uV} T ψ N k hk ⋙
        SmoothRep.twistFunctor (T.determinantPowerCharacter (N - k) s)
          (T.isOpen_ker_determinantPowerCharacter (N - k) s)))

end Langlands.Derivative
