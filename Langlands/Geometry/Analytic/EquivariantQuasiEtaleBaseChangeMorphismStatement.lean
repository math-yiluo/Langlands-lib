import Langlands.Geometry.Analytic.EquivariantCompactProbeTopology
import Langlands.Geometry.Analytic.EquivariantSiteBaseChange

/-! # Equivariant quasi-étale base change as a morphism of compact-probe sites -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.SpaceWithOperators

open _root_.CategoryTheory

/-- Over a fixed complete ground field, the quasi-étale pullback functor of a
morphism of spaces with operators is representably flat and continuous for the
equivariant compact-probe quasi-étale topologies. -/
def EquivariantQuasiEtaleBaseChangeMorphismStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {Y X : SpaceWithOperators.{u, v, v, z} K} (f : Y ⟶ X),
    RepresentablyFlat (quasiEtalePullbackFunctor f) ∧
      (quasiEtalePullbackFunctor f).IsContinuous (equivariantCompactProbeQuasiEtaleTopology X.space)
        (equivariantCompactProbeQuasiEtaleTopology Y.space)

end Langlands.Analytic.SaturatedAtlasPresentation.SpaceWithOperators
