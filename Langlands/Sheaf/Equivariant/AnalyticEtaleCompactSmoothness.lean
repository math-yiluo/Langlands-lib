import Langlands.Sheaf.Equivariant.AnalyticRepSmoothness
import Langlands.Cohomology.AnalyticEtaleCompactComparison.Statement
import Langlands.Representation.Smooth.Transfer.PullbackProof

/-!
# Smoothness of the action of `G` on `H^q_c(X, b^*F)`, granting Berkovich's comparison

Berkovich's Corollary 1.5.2(i) says that the comparison maps `H^q_c(X{G}, F) → H^q_c(X, b^*F)`
are isomorphisms for every étale `G`-sheaf `F`, and "in particular, the canonical action of `G`
on the groups `H^q_c(X, b^*F)` is discrete". The first assertion is Worker 16's statement
`AnalyticEtaleCompactComparisonStatement`, which is not proved. This module derives the second
assertion from it: under the hypotheses of the statement, the comparison maps are bijective,
the canonical action of `G` on `H^q_c(X, b^*F)` is smooth, and the comparison is an
isomorphism of smooth representations. The restriction of this action to any subgroup of `G`
is then smooth as well.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Cohomology.AnalyticEtaleCompactComparison

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- Berkovich's Corollary 1.5.2(i) for étale sheaves, stated as
`AnalyticEtaleCompactComparisonStatement`, implies that for a Hausdorff `X` whose points all
underlie `L`-valued points, with a continuous action, the comparison
`H^q_c(X{G}, F) → H^q_c(X, b^*F)` is bijective. -/
theorem etaleCompactComparison_app_bijective_of_statement
    (hB : AnalyticEtaleCompactComparisonStatement L X h G ρ R)
    (hT : T2Space (localizedSpaceFunctor.obj X))
    (hS : Function.Surjective (pointProjection L X)) (hρ : IsContinuousAction ρ) (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Function.Bijective ((etaleCompactComparison L ρ h R q).app F).hom := by
  have := hB hT hS hρ q
  exact ConcreteCategory.bijective_of_isIso ((etaleCompactComparison L ρ h R q).app F)

/-- Granting `AnalyticEtaleCompactComparisonStatement` (Berkovich, Corollary 1.5.2(i), étale
case): for a Hausdorff `X` whose points all underlie `L`-valued points, with a continuous
action, the canonical action of `G` on `H^q_c(X, b^*F)` is smooth. -/
theorem etaleRestrictionCompactCohomologyAction_isSmooth_of_statement
    (hB : AnalyticEtaleCompactComparisonStatement L X h G ρ R)
    (hT : T2Space (localizedSpaceFunctor.obj X))
    (hS : Function.Surjective (pointProjection L X)) (hρ : IsContinuousAction ρ) (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Langlands.IsSmooth (etaleRestrictionCompactCohomologyAction L ρ h R q F) :=
  etaleRestrictionCompactCohomologyAction_isSmooth_of_surjective L ρ h R q F
    (etaleCompactComparison_app_bijective_of_statement L ρ h R hB hT hS hρ q F).2

/-- Granting `AnalyticEtaleCompactComparisonStatement`: for a Hausdorff `X` whose points all
underlie `L`-valued points, with a continuous action, the comparison
`H^q_c(X{G}, F) → H^q_c(X, b^*F)` is an isomorphism of smooth representations. -/
def etaleCompactComparisonSmoothIsoOfStatement
    (hB : AnalyticEtaleCompactComparisonStatement L X h G ρ R)
    (hT : T2Space (localizedSpaceFunctor.obj X))
    (hS : Function.Surjective (pointProjection L X)) (hρ : IsContinuousAction ρ) (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    (etaleGSheafCompactCohomology L ρ h R q).obj F ≅
      etaleRestrictionCompactCohomologySmoothRep L ρ h R q F
        (etaleCompactComparison_app_bijective_of_statement L ρ h R hB hT hS hρ q F).2 :=
  etaleCompactComparisonSmoothIso L ρ h R q F
    (etaleCompactComparison_app_bijective_of_statement L ρ h R hB hT hS hρ q F)

/-- Granting `AnalyticEtaleCompactComparisonStatement`: for a Hausdorff `X` whose points all
underlie `L`-valued points, with a continuous action, the restriction to any subgroup `H` of
the canonical action of `G` on `H^q_c(X, b^*F)` is smooth (`H` with the subspace topology). -/
theorem etaleRestrictionCompactCohomologyAction_comp_subtype_isSmooth_of_statement
    (hB : AnalyticEtaleCompactComparisonStatement L X h G ρ R)
    (hT : T2Space (localizedSpaceFunctor.obj X))
    (hS : Function.Surjective (pointProjection L X)) (hρ : IsContinuousAction ρ) (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (H : Subgroup G) :
    Langlands.IsSmooth ((etaleRestrictionCompactCohomologyAction L ρ h R q F).comp H.subtype) :=
  isSmooth_comp H.subtype continuous_subtype_val
    (etaleRestrictionCompactCohomologyAction_isSmooth_of_statement L ρ h R hB hT hS hρ q F)

end Langlands.Sheaf.Equivariant.Analytic
