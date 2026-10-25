import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Parabolic.ComposedFunctors
import Langlands.Representation.Induction.Parabolic

/-! Function-preserving comparison of direct composed and flattened induction. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF uV

/-- Direct normalized induction from the composed parabolic agrees with standard
flattened induction through an equivalence preserving every function value in
both directions. This declaration states the comparison; it does not prove it. -/
def ComposedFlattenedInductionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : BlockShape n) (S : BlockRefinement B)
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (σ : Representation ℂ (refinedLevi F.Carrier B S) V),
      letI := T.generalLinearTopologicalGroup n
      ∃ E : (T.normalizedComposedInduced B S σ).Equiv
          (T.normalizedParabolicInduced (B.flatten S)
            (σ.comp (flattenedLeviEquiv F.Carrier B S).toMonoidHom)),
        (∀ f (g : GeneralLinear n F.Carrier),
          Induction.eval _ _ (E f) g = Induction.eval _ _ f g) ∧
        (∀ f (g : GeneralLinear n F.Carrier),
          Induction.eval _ _ (E.symm f) g = Induction.eval _ _ f g)

end Langlands.Parabolic
