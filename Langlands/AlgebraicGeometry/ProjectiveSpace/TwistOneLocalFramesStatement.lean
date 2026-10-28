import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOne
import Langlands.AlgebraicGeometry.Modules.SectionLocus
import Langlands.AlgebraicGeometry.Picard.LineBundle

/-! # Coordinate frames and local rank one of `𝒪(1)` on projective space -/

universe u

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- For every commutative ring `R : Type u` and every `n : ℕ`, two properties of the actual
twisting sheaf `twistOne R n = 𝒪(1)` on `ProjectiveSpace R n` hold. First, for each `i`, the
restriction to the coordinate open `D₊(X i)` of the morphism `𝒪 → 𝒪(1)` sending `1` to the
coordinate section `X i` is an isomorphism. Second, `𝒪(1)` is locally isomorphic to the
structure sheaf. No hypothesis is placed on `R` or `n`. This proposition is a statement
target, not a proof of these properties. -/
def ProjectiveSpaceTwistOneLocalFramesStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ),
    (∀ i : Fin (n + 1),
      Langlands.SchemeModule.TrivializesOn (twistOne R n)
        (twistOneCoordinate R n i) (projectiveSpaceCoordinateOpen R n i)) ∧
    Langlands.AlgebraicGeometry.Picard.IsLocallyFreeRankOne (twistOne R n)

end Langlands.AlgebraicGeometry
