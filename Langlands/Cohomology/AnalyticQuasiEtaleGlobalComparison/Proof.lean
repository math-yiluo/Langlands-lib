import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactTupleComparison
import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactTupleConeAssembly
import Langlands.Geometry.Analytic.QuasiEtaleLiftCompatibilityProof

/-! # Compact quasi-étale global comparison -/

noncomputable section

universe u v uL z

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Small.{max u (v + 1) uL} G]
variable (ρ : G →* Aut X)
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Berkovich's compact quasi-étale global cohomology comparison. -/
theorem analyticQuasiEtaleGlobalComparison :
    AnalyticQuasiEtaleGlobalComparisonStatement.{u, v, uL, z} X G ρ R :=
  analyticQuasiEtaleGlobalComparison_of_tupleCones_liftCompatibilityStatement.{u, v, uL, z}
    ρ R compactCompatibleTupleCones (quasiEtaleLiftCompatibility K)

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
