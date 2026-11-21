import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactTupleComparison
import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactTupleConeAssembly
import Langlands.Geometry.Analytic.QuasiEtaleLiftCompatibilityProof

/-! # Acyclicity after restriction of injective quasi-étale G-sheaves -/

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

/-- The ordinary restriction of an injective discrete quasi-étale equivariant
module sheaf on a compact Hausdorff base has zero higher cohomology. -/
theorem quasiEtaleRestrictedInjectivesAcyclic
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] :
    QuasiEtaleRestrictedInjectivesAcyclicStatement.{u, v, uL, z} X G ρ R := by
  have hCones : CompactCompatibleTupleConesStatement ρ := compactCompatibleTupleCones (ρ := ρ)
  have := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  have := quasiEtale_hasSheafify.{u, v, uL} X R
  have := quasiEtale_enoughInjectives.{u, v, uL} X R
  have := quasiEtale_wEqualsLocallyBijective.{u, v, uL} X R
  apply restrictedInjectivesAcyclic_of_compactCompatibleCech.{u, v, uL, z}
    ρ R hCones.cechPresentation
  intro hX hρ I hI
  have : Injective I := hI
  exact homAcyclic_of_compactTupleCones.{u, v, uL, z} ρ R hCones
    (hasCompatibleCompactQuasiEtaleLifts_of_compatibilityStatement
      (quasiEtaleLiftCompatibility K) hX.2 hρ) I

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
