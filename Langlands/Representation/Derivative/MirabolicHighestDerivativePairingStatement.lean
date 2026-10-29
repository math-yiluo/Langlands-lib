import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Filtration.InvariantBilinear

/-!
# Highest derivatives of nondegenerate mirabolic pairings

Let `A`, `B` be smooth complex representations of the mirabolic group `P_(N+1)`,
paired by a form with determinant covariance that is nondegenerate in `A`. If `k`
is the highest order with a nonzero derivative of `A`, the order-`k` derivatives
of `A` and `B` admit an invariant pairing nondegenerate in the derivative of `A`.
This module states that assertion and proves nothing.
-/

namespace Langlands.Derivative

open GeneralLinear HarmonicAnalysis

open scoped NNReal

/-- Bernstein–Zelevinsky (1977), Proposition 3.8, for the actual order-`k` derivatives
`mirabolicDerivativeOfOrder T ψ N k hk` of `P_(N+1)`-representations `A` and `B` in
independent carrier universes. The source `Δ_P`-pairing is a form with simultaneous
covariance `g ↦ |det g|`; the conclusion is an invariant (covariance one) pairing. -/
def MirabolicHighestDerivativePairingStatement.{uF, uV, uW} {p : ℕ} [Fact p.Prime]
    (F : PadicField.{uF} p) (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (N : ℕ)
    (A : SmoothRep.{0, uF, uV} ℂ (mirabolic N F.Carrier))
    (B : SmoothRep.{0, uF, uW} ℂ (mirabolic N F.Carrier))
    (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1),
    Nontrivial ((mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk).obj A) →
    (∀ (j : ℕ) (hj : 0 < j ∧ j ≤ N + 1), k < j →
      Subsingleton ((mirabolicDerivativeOfOrder.{uF, uV} T ψ N j hj).obj A)) →
    ∀ β : InvariantBilinear.forms A.representation B.representation
        (fun g => ((((T.determinantNorm (N + 1)) g.val : ℝ≥0) : ℝ) : ℂ)),
      (∀ v : A, (∀ w : B, β.val v w = 0) → v = 0) →
      ∃ γ : InvariantBilinear.forms
          ((mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk).obj A).representation
          ((mirabolicDerivativeOfOrder.{uF, uW} T ψ N k hk).obj B).representation
          (fun _ => (1 : ℂ)),
        ∀ v : (mirabolicDerivativeOfOrder.{uF, uV} T ψ N k hk).obj A,
          (∀ w : (mirabolicDerivativeOfOrder.{uF, uW} T ψ N k hk).obj B,
            γ.val v w = 0) → v = 0

end Langlands.Derivative
