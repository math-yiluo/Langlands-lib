import Langlands.Representation.Derivative.Homogeneity
import Langlands.Representation.Classification.StrongIndecomposability

/-!
# Highest-derivative strong indecomposability reduction

This proposition records positive-order detection and Zelevinsky's
homogeneity/highest-derivative criterion. It supplies no analytic proof.
-/

noncomputable section

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Positive derivative level and the strong-indecomposability criterion at
the actual highest positive derivative of a nonzero mirabolic representation. -/
def MirabolicStrongIndecomposabilityReduction : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic N F.Carrier)),
    (Nontrivial A → 0 < level T ψ A) ∧
      ∀ (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1),
        Nontrivial A → k = level T ψ A →
          (Classification.IsStronglyIndecomposable A.representation ↔
            IsHomogeneous T ψ A ∧
              Classification.IsStronglyIndecomposable
                ((mirabolicDerivativeOfOrder T ψ N k hk).obj A).representation)

end Langlands.Derivative
