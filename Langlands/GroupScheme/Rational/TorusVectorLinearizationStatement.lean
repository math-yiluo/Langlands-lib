import Langlands.GroupScheme.Rational.CentralVectorQuotientStatement

/-! # Linear coordinates for arbitrary torus actions on vector groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Every actual action of a torus on a vector group admits natural coordinates
of the given dimension in which the action is linear on every scheme test.
The torus need not be split over the ground field. -/
def TorusVectorActionLinearizationStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T V : GroupScheme (Spec (CommRingCat.of k))) (n : ℕ),
    IsTorus T → IsVectorGroupOfDimension V n → ∀ a : AutomorphicAction T V,
      ∃ e : ∀ W : Over (Spec (CommRingCat.of k)),
        (W ⟶ V.X) ≃* Multiplicative (Fin n → Γ(W.left, ⊤)),
        IsLinearVectorCoordinates a e

end Langlands.GroupScheme.RelativeRoot
