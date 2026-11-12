import Langlands.Geometry.Analytic.InducedSpaceAdjunction
import Langlands.Geometry.Analytic.QuasiEtaleSite

/-! # Statement: induction preserves étale and quasi-étale morphisms -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

/-- Statement: for a subgroup `H` of a group `G` and a morphism `f : X ⟶ X'` of analytic spaces
with actions of `H`, if the underlying morphism of `f` is quasi-étale (resp. étale), so is the
underlying morphism of the induced morphism `X_{G/H} ⟶ X'_{G/H}`. -/
def MorphismPropertyStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : Type z) [Group G] (H : Subgroup G)
    {X X' : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H} (f : X ⟶ X'),
    (quasiEtale f.hom → quasiEtale ((inductionFunctor H).map f).hom) ∧
      (etale f.hom → etale ((inductionFunctor H).map f).hom)

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
