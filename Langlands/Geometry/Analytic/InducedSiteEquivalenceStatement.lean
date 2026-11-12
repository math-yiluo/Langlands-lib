import Langlands.Geometry.Analytic.InducedEquivariantSite

/-! # Statement: the quasi-étale sites of `X(H)` and `X_{G/H}(G)` are equivalent -/

universe u v z

open CategoryTheory

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

/-- Statement (Berkovich 1996, Example 1.2.1(i), quasi-étale case): for an open subgroup `H`
of a topological group `G` and an `H`-space `X`, induction `U(H) ↦ U_{G/H}(G)` is an
equivalence `Qét(X(H)) ≌ Qét(X_{G/H}(G))` that preserves and reflects coverings. The functor
is defined given the continuity and morphism-property statements for induction, which are
taken as hypotheses. -/
def QuasiEtaleSiteEquivalenceStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H : Subgroup G)
    (hH : IsOpen (H : Set G)) (hC : ContinuityStatement.{u, v, z})
    (hQ : MorphismPropertyStatement.{u, v, z}) (X : GSpace.{u, max z v, max z v} K H),
    (quasiEtaleSiteInduction hH hC hQ X).IsEquivalence ∧
      ∀ (U : EquivariantQuasiEtaleSite X) (R : Presieve U),
        R.map (quasiEtaleSiteInduction hH hC hQ X) ∈
            equivariantQuasiEtalePrecoverage _ ((quasiEtaleSiteInduction hH hC hQ X).obj U) ↔
          R ∈ equivariantQuasiEtalePrecoverage X U

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace
