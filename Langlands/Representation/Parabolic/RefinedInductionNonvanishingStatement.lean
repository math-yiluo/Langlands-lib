import Langlands.Representation.Geometric.RefinementFunctors
import Langlands.Representation.Induction.CompactLocalSection

/-! Evaluation and nonvanishing targets for the actual refined induction. -/

noncomputable section

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- Evaluation at identity is surjective for smooth inducing data, and the actual
normalized refined induction of a nonzero carrier has a nonzero carrier. -/
def NormalizedRefinedInductionNonvanishingStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B),
      letI := T.leviTopologicalGroup B
      ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ (refinedLevi F.Carrier B S) V),
        IsSmooth σ →
          let σP := twist (T.refinedParabolicHalfModulus B S)
            (σ.comp (refinedLeviProjection F.Carrier B S))
          let I : Rep.{max uF uV} ℂ (B.Levi F.Carrier) :=
            Rep.of (T.normalizedRefinedInduced B S σ)
          Function.Surjective (fun f : I =>
            Induction.eval (refinedParabolic F.Carrier B S) σP f 1) ∧
          (Nontrivial V → Nontrivial I)

end Langlands.Parabolic
