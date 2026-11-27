import Langlands.Cohomology.AnalyticEtaleCompactComparison.GeometryReduction
import Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.Proof

/-!
# Berkovich's comparison `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` (étale): proof

Proof of `AnalyticEtaleCompactComparisonStatement`, Berkovich, *Étale equivariant sheaves on
p-adic analytic spaces*, Corollary 1.5.2(i), first assertion, for étale `G`-sheaves with
supports in `L`-valued points. The reduction `compactComparison_of_compactAcyclic` proves the
statement from compact acyclicity of the restrictions of injective étale `G`-sheaves, and
`analyticEtaleRestrictedInjectiveAcyclic` proves that acyclicity.
-/

set_option autoImplicit false

namespace Langlands.Cohomology.AnalyticEtaleCompactComparison

open _root_.CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic
open Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

universe u v uL z

/-- Berkovich, Corollary 1.5.2(i), first assertion, étale case: if `|X|` is Hausdorff, every
point of `X` underlies an `L`-valued point and the action `ρ` of `G` is continuous, then for
every `q` the comparison `etaleCompactComparison L ρ h R q : H^q_c(X{G}, F) → H^q_c(X, b^*F)`
is an isomorphism, naturally in the étale `G`-sheaf of `R`-modules `F`. -/
theorem analyticEtaleCompactComparison
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] :
    AnalyticEtaleCompactComparisonStatement L X h G ρ R :=
  compactComparison_of_compactAcyclic L X h G ρ R
    (analyticEtaleRestrictedInjectiveAcyclic L X h G ρ R).1

end Langlands.Cohomology.AnalyticEtaleCompactComparison
