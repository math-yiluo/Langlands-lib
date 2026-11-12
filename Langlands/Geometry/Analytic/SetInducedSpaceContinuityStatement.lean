import Langlands.Geometry.Analytic.SetInducedSpace
import Langlands.Geometry.Analytic.ContinuousAnalyticAction
import Mathlib.Topology.Algebra.Group.Basic

/-! # Statement: the spaces `X_Σ` of discrete `G`-sets are `G`-spaces -/

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace

/-- Statement (Berkovich 1996, §1.2): for a `G`-space `X` and a `G`-set `S` all of whose
stabilizers are open, Berkovich's space `X_S` is a `G`-space. -/
def ContinuityStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (X : Action (LocalizedCategory.{u, max z v, max z v} (K := K)) G)
    (S : Type z) [MulAction G S],
    (∀ s : S, IsOpen (MulAction.stabilizer G s : Set G)) →
      gSpaceProperty.{u, max z v, max z v} K G X →
        gSpaceProperty.{u, max z v, max z v} K G (setInduced X S)

end Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace
