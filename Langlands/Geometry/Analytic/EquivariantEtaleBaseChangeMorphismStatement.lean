import Langlands.Geometry.Analytic.EquivariantEtalePretopology
import Langlands.Geometry.Analytic.EquivariantSiteBaseChange

/-! # Equivariant étale base change as a morphism of sites -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.SpaceWithOperators

open _root_.CategoryTheory

/-- Over a fixed complete ground field, the étale pullback functor of a morphism
of spaces with operators is representably flat and continuous for the equivariant
étale topologies. -/
def EquivariantEtaleBaseChangeMorphismStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    {Y X : SpaceWithOperators.{u, v, v, z} K} (f : Y ⟶ X),
    RepresentablyFlat (etalePullbackFunctor f) ∧
      (etalePullbackFunctor f).IsContinuous (equivariantEtaleTopology X.space)
        (equivariantEtaleTopology Y.space)

end Langlands.Analytic.SaturatedAtlasPresentation.SpaceWithOperators
