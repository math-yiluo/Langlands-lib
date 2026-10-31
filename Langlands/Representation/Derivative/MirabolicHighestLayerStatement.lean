import Langlands.Representation.Derivative.Homogeneity

/-! # The actual highest mirabolic layer

This proposition isolates the analytic layer and lattice inputs to the
highest-derivative criterion. It contains no strong-indecomposability claim.
-/

noncomputable section

namespace Langlands.Derivative

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- A nonzero actual highest layer, its derivative lattice, and essentiality. -/
def MirabolicHighestLayerStatement : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)
    (N : ℕ) (A : SmoothRep.{0, uF, uV} ℂ (GeneralLinear.mirabolic N F.Carrier))
    (k : ℕ) (hk : 0 < k ∧ k ≤ N + 1),
    Nontrivial A → k = level T ψ A →
      ∃ U : Subrepresentation A.representation,
        U ≠ ⊥ ∧
          Nonempty (Subrepresentation
            ((mirabolicDerivativeOfOrder T ψ N k hk).obj A).representation ≃o Set.Iic U) ∧
          (IsHomogeneous T ψ A ↔
            ∀ S : Subrepresentation A.representation, S ≠ ⊥ → U ⊓ S ≠ ⊥)

end Langlands.Derivative
