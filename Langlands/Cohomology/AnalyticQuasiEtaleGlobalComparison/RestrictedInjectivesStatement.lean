import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.Statement

/-! # Acyclicity of the restrictions of injective quasi-étale `G`-sheaves -/

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

/-- The vanishing claim in the quasi-étale proof of Berkovich, Theorem 1.6.1(ii),
for sheaves of modules: on compact `X`, restriction of an injective quasi-étale
`G`-sheaf has zero higher ordinary quasi-étale cohomology. -/
def QuasiEtaleRestrictedInjectivesAcyclicStatement
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  IsCompactSpace X → IsContinuousAction ρ →
    ∀ I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R), Injective I →
      ∀ q : ℕ, IsZero ((quasiEtaleCohomology.{u, v, uL} X R (q + 1)).obj
        ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I))

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
