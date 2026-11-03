import Langlands.GroupScheme.Rational.CentralVectorQuotientStatement

/-! # Linear coordinates for actual split-torus actions on vector groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- Over an algebraically closed field, an actual split-torus action on a
vector group admits natural linear coordinates, including the fixed part. -/
def SplitTorusVectorLinearizationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (V : GroupScheme (Spec (CommRingCat.of k))),
    IsVectorGroup V →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus S.toGrp → ∀ b : AutomorphicAction S.toGrp V,
      ∃ (n : ℕ) (e : ∀ T : Over (Spec (CommRingCat.of k)),
        (T ⟶ V.X) ≃* Multiplicative (Fin n → Γ(T.left, ⊤))),
        IsLinearVectorCoordinates b e

end Langlands.GroupScheme.RelativeRoot
