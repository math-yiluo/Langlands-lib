import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Derivative.MirabolicMinusExactnessStatement

/-!
# Exactness of the general-linear derivatives

Every actual Bernstein–Zelevinsky derivative `π ↦ π^(k)` from smooth complex
representations of `GL_N` to those of `GL_(N-k)`, for every order `k ≤ N`, carries
short exact sequences of intertwiners to short exact sequences. This module states
that assertion and proves nothing.
-/

namespace Langlands.Derivative

open CategoryTheory GeneralLinear HarmonicAnalysis

/-- Exactness of the actual derivative `generalLinearDerivative T ψ N k hk` for every
supplied nontrivial unitary additive character `ψ`, every rank `N` and every order
`k ≤ N`. -/
def GeneralLinearDerivativeExactnessStatement.{uF, uV} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N k : ℕ) (hk : k ≤ N),
    Mirabolic.MapsShortExactIntertwiners (generalLinearDerivative.{uF, uV} T ψ N k hk)

end Langlands.Derivative
