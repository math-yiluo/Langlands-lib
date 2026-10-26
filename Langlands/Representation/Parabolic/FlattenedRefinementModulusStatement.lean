import Langlands.Representation.Geometric.FlattenedLevi
import Langlands.Representation.Parabolic.RefinementComposition

/-! The full positive modulus comparison for a flattened ordered block refinement. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric

universe uF

/-- The composed modulus of an ordered block refinement, pulled back along the
constructed flattened Levi equivalence, is the standard full modulus of the
flattened shape. This is an equality of positive characters, including rank zero. -/
def FlattenedRefinementModulusStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ) (B : GeneralLinear.BlockShape n) (S : BlockRefinement B),
    (T.composedLeviModulus B S).comp
      (Geometric.flattenedLeviEquiv F.Carrier B S).toMonoidHom =
        T.leviModulus (B.flatten S)

end Langlands.Parabolic
