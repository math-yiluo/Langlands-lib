import Langlands.AlgebraicGeometry.ProjectiveSpace.TwistOne
import Langlands.AlgebraicGeometry.Modules.SectionLocus

/-! # The whole generation opens of the coordinate sections of `𝒪(1)` -/

universe u

namespace Langlands.AlgebraicGeometry

/-- For every commutative ring `R : Type u`, every `n : ℕ` and every `i : Fin (n + 1)`, the
whole generation open of the coordinate section `X i` of the actual twisting sheaf
`twistOne R n = 𝒪(1)` on `ProjectiveSpace R n` is exactly the coordinate open `D₊(X i)`.
The generation open is the published `trivializationOpen`, the supremum of all opens on which
the morphism `𝒪 → 𝒪(1)` sending `1` to `X i` restricts to an isomorphism. The two sides are
equal as opens of the scheme. No hypothesis is placed on `R`, `n` or `i`. This proposition is
a statement target, not a proof of this equality. -/
def ProjectiveSpaceCoordinateGenerationOpenStatement : Prop :=
  ∀ (R : Type u) [CommRing R] (n : ℕ) (i : Fin (n + 1)),
    Langlands.SchemeModule.trivializationOpen (twistOne R n)
      (twistOneCoordinate R n i) = projectiveSpaceCoordinateOpen R n i

end Langlands.AlgebraicGeometry
