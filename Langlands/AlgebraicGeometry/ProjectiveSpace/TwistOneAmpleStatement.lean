import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOne
import Langlands.AlgebraicGeometry.Picard.Ample

/-! # Ampleness of the actual `𝒪(1)` on projective space -/

universe u

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- For every commutative ring `R : Type u` and every `n : ℕ`, the actual twisting sheaf
`twistOne R n = 𝒪(1)` on `ProjectiveSpace R n` underlies a line bundle that is ample in the
published sense. The equality fixes the underlying module to `twistOne R n` itself; the
existential only packages its local rank-one property. No hypothesis is placed on `R` or `n`.
This proposition is a statement target, not a proof of these properties. -/
def ProjectiveSpaceTwistOneAmpleStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    ∃ M : Langlands.AlgebraicGeometry.Picard.LineBundle (ProjectiveSpace R n),
      M.obj = twistOne R n ∧ M.IsAmple

end Langlands.AlgebraicGeometry
