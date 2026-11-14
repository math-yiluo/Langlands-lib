import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology

/-!
# Berkovich's comparison `H^q(X{G}, F) ≅ H^q(X, b^*F)` for compact `X` (étale)

Statement, without proof, of Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
Theorem 1.6.1(ii), for étale sheaves: if a topological group `G` acts continuously on a compact
analytic space `X`, then for every étale `G`-sheaf `F` the comparison maps
`H^q(X{G}, F) → H^q(X, b^*F)` are isomorphisms in every degree `q`.
-/

namespace Langlands.Cohomology.AnalyticEtaleGlobalComparison

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

/-- Berkovich, Theorem 1.6.1(ii), étale case: for a continuous action `ρ` of a topological group
`G` on a compact analytic space `X` (compact and Hausdorff), and a commutative ring `R`, the
comparison `etaleComparison ρ R q : H^q(X{G}, F) → H^q(X, b^*F)` is an isomorphism, naturally in
the étale `G`-sheaf of `R`-modules `F`, for every `q`. The smallness of `G` and the admissible
refinement condition are needed to define the source. -/
def AnalyticEtaleGlobalComparisonStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  IsCompactSpace X → IsContinuousAction ρ →
    ∀ q : ℕ, IsIso (etaleComparison.{u, v, uL} ρ R q)

end Langlands.Cohomology.AnalyticEtaleGlobalComparison
