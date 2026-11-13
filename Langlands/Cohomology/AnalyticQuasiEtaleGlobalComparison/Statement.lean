import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology

/-!
# Berkovich's comparison `H^q(X{G}, F) ≅ H^q(X, b^*F)` for compact `X`

Statement, without proof, of Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*,
Theorem 1.6.1(ii), for quasi-étale sheaves: if a topological group `G` acts continuously on a
compact analytic space `X`, then for every quasi-étale `G`-sheaf `F` the comparison maps
`H^q(X{G}, F) → H^q(X, b^*F)` are isomorphisms in every degree `q`.
-/

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

/-- Berkovich, Theorem 1.6.1(ii), quasi-étale case: for a continuous action `ρ` of a topological
group `G` on a compact analytic space `X` (compact and Hausdorff), and a commutative ring `R`, the
comparison `quasiEtaleComparison ρ R q : H^q(X{G}, F) → H^q(X, b^*F)` is an isomorphism, naturally
in the quasi-étale `G`-sheaf of `R`-modules `F`, for every `q`. The smallness of `G` and the finite
equivariant refinement condition are needed to define the source. -/
def AnalyticQuasiEtaleGlobalComparisonStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  IsCompactSpace X → IsContinuousAction ρ →
    ∀ q : ℕ, IsIso (quasiEtaleComparison.{u, v, uL} ρ R q)

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
