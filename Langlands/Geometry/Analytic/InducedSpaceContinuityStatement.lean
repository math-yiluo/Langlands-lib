import Langlands.Geometry.Analytic.InducedAnalyticSpace
import Langlands.Geometry.Analytic.ContinuousAnalyticAction
import Mathlib.Topology.Algebra.Group.Basic

/-! # Statement: induced spaces of `H`-spaces are `G`-spaces -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

/-- Statement (Berkovich 1996, 1.1.2): for an open subgroup `H` of a topological group `G` and
an `H`-space `X` (Hausdorff, with continuous action), the induced space `X_{G/H}` is a
`G`-space. -/
def ContinuityStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G),
    IsOpen (H : Set G) →
    ∀ X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) H,
      gSpaceProperty.{u, max z v, max z v} K H X →
        gSpaceProperty.{u, max z v, max z v} K G (inducedAction H X)

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
