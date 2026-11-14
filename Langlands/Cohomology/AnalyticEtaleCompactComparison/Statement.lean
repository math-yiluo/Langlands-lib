import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison

/-!
# Berkovich's comparison `H^q_c(X{G}, F) ≅ H^q_c(X, b^*F)` (étale)

Statement, without proof, of Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
Corollary 1.5.2(i), first assertion: if a topological group `G` acts continuously on a Hausdorff
analytic space `X`, then for every étale `G`-sheaf `F` the comparison maps
`H^q_c(X{G}, F) → H^q_c(X, b^*F)` are isomorphisms in every degree `q`. Supports are taken in the
`L`-valued points of `X`, and every point of `X` is assumed to underlie an `L`-valued point, so
that these supports see every point of `X`, as Berkovich's supports do.
-/

namespace Langlands.Cohomology.AnalyticEtaleCompactComparison

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

/-- Berkovich, Corollary 1.5.2(i), first assertion, étale case: let `ρ` be an action of a
topological group `G` by automorphisms over `K` of an analytic space `X`, `L` a normed field over
`K` whose `L`-valued points of `X` satisfy the point axioms `h`, and `R` a commutative ring. If the
underlying space of `X` is Hausdorff, every point of it underlies an `L`-valued point, and `ρ` is
continuous, then for every `q` the comparison
`etaleCompactComparison L ρ h R q : H^q_c(X{G}, F) → H^q_c(X, b^*F)` is an isomorphism, naturally
in the étale `G`-sheaf of `R`-modules `F`. The smallness of `G` and the admissible refinement
condition are needed to define the source. -/
def AnalyticEtaleCompactComparisonStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  T2Space (localizedSpaceFunctor.obj X) → Function.Surjective (pointProjection L X) →
    IsContinuousAction ρ → ∀ q : ℕ, IsIso (etaleCompactComparison L ρ h R q)

end Langlands.Cohomology.AnalyticEtaleCompactComparison
