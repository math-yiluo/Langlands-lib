import Langlands.Representation.Derivative.Iteration

/-!
# Finite-length preservation by the general-linear derivatives

Every actual Bernstein–Zelevinsky derivative `π ↦ π^(k)` from smooth complex
representations of `GL_N` to those of `GL_(N-k)`, for every order `k ≤ N`, sends a
representation of finite group-algebra length to one of finite group-algebra length.
This module states that assertion and proves nothing.
-/

namespace Langlands.Derivative

open CategoryTheory GeneralLinear HarmonicAnalysis

/-- Finite length of the actual derivative `(generalLinearDerivative T ψ N k hk).obj A`
of every finite-length `A`, for every supplied nontrivial unitary additive character `ψ`,
every rank `N` and every order `k ≤ N`. -/
def GeneralLinearDerivativeFiniteLengthStatement.{uF, uV} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N k : ℕ) (hk : k ≤ N)
    (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear N F.Carrier)),
    A.HasFiniteLength →
      ((generalLinearDerivative.{uF, uV} T ψ N k hk).obj A).HasFiniteLength

end Langlands.Derivative
