import Langlands.Sheaf.Equivariant.AnalyticEtaleGlobalComplex

/-!
# Derived global étale comparison on compact analytic spaces

The comparison of global-section complexes induces the comparison in
Berkovich's Theorem 1.6.1(ii) on cohomology. Its derived version concerns
the complexes of modules obtained by forgetting the action on the source.
-/

set_option autoImplicit false

namespace Langlands.Cohomology.AnalyticEtaleGlobalComparison

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z wRep wMod

/-- On a compact Hausdorff analytic space with a continuous group action,
the canonical map from derived smooth global sections, with the action
forgotten, to derived global sections of the restriction is invertible. -/
def AnalyticEtaleGlobalDerivedComparisonStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  IsCompactSpace X → IsContinuousAction ρ →
    ∀ [HasDerivedCategory.{wRep} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
      [HasDerivedCategory.{wMod} (ModuleCat.{max u (v + 1) uL} R)],
      IsIso (etaleComplexComparison.{u, v, uL} ρ R)

end Langlands.Cohomology.AnalyticEtaleGlobalComparison
