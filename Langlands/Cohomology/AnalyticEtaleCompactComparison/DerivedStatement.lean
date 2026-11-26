import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison

/-!
# The derived étale compact-support comparison

The comparison morphism of compact-section complexes induces the cohomology
maps of Berkovich's Corollary 1.5.2(i). This states its invertibility in the
derived category of modules after forgetting the acting group.
-/

set_option autoImplicit false

namespace Langlands.Cohomology.AnalyticEtaleCompactComparison

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z wRep wMod

/-- The canonical map from derived smooth compact sections, with the action
forgotten, to the derived ordinary compact sections of the restriction is
an isomorphism of functors. -/
def AnalyticEtaleCompactDerivedComparisonStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  T2Space (localizedSpaceFunctor.obj X) → Function.Surjective (pointProjection L X) →
    IsContinuousAction ρ →
    ∀ [HasDerivedCategory.{wRep} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
      [HasDerivedCategory.{wMod} (ModuleCat.{max u (v + 1) uL} R)],
      IsIso (etaleCompactComplexComparison L ρ h R)

end Langlands.Cohomology.AnalyticEtaleCompactComparison
