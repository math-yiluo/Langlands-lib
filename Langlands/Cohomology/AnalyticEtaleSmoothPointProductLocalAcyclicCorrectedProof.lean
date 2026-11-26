import Langlands.Cohomology.AnalyticEtaleGaloisCoinducedLocalAcyclicProof
import Langlands.Cohomology.AnalyticEtaleSmoothPointProductGaloisReduction

/-! # Local acyclicity of actual restricted smooth point products, for a topological group -/

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open _root_.CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- For a topological group `G`, positive ordinary higher direct images of the actual
restricted smooth point product vanish on injective independent coefficient diagrams. -/
theorem analyticEtaleSmoothPointProductLocalAcyclicCorrected
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    (R : Type (max u (v + 1) uL)) [CommRing R]
    (G : Type z) [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
    [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)] :
    AnalyticEtaleSmoothPointProductLocalAcyclicCorrectedStatement L X h R G ρ :=
  analyticEtaleSmoothPointProductLocalAcyclicCorrected_of_galoisCoinduced L X h R G ρ
    (analyticEtaleGaloisCoinducedLocalAcyclic L X R G ρ)

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
