import Langlands.Geometry.Analytic.SetInducedSite
import Mathlib.CategoryTheory.Functor.Flat

/-! # Statement: `Σ ↦ X_Σ(G)` defines morphisms of sites `X(G)_qét → P(G)` and
`X(G)_ét → P(G)` -/

universe u v z

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace

/-- Statement (Berkovich 1996, §1.2): for a `G`-space `X`, the functor `γ : Σ ↦ X_Σ(G)` from
`P(G)` to `Qét(X(G))` (resp. `Ét(X(G))`) is representably flat and continuous, so it defines a
morphism of sites `X(G)_qét → P(G)` (resp. `X(G)_ét → P(G)`). The functor is defined given
the continuity statement for `X_Σ` and the statement on morphisms out of disjoint unions,
which are taken as hypotheses. -/
def MorphismOfSitesStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hC : ContinuityStatement.{u, v, z}) (hD : SigmaDescStatement.{u, v, z})
    (X : GSpace.{u, max z v, max z v} K G),
    (RepresentablyFlat (quasiEtaleSiteFunctor hC X hD) ∧
        (quasiEtaleSiteFunctor hC X hD).IsContinuous (DiscreteGSet.topology G)
          (equivariantQuasiEtaleTopology X)) ∧
      (RepresentablyFlat (etaleSiteFunctor hC X hD) ∧
        (etaleSiteFunctor hC X hD).IsContinuous (DiscreteGSet.topology G)
          (equivariantEtaleTopology X))

end Langlands.Analytic.SaturatedAtlasPresentation.SetInducedSpace
