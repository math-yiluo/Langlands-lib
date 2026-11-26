import Langlands.Cohomology.AnalyticEtalePointedGaloisRefinementProof

/-! # Local acyclicity of coinduced Galois fixed sections -/

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open _root_.CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Coinduced Galois fixed sections give vanishing ordinary higher direct images
for the restriction of an étale `G`-sheaf. -/
theorem analyticEtaleGaloisCoinducedLocalAcyclic
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (R : Type (max u (v + 1) uL)) [CommRing R]
    (G : Type z) [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
    [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)] :
    AnalyticEtaleGaloisCoinducedLocalAcyclicStatement L X R G ρ :=
  analyticEtaleGaloisCoinducedLocalAcyclic_of_relativeRefinement L R
    (pointedAnalyticGaloisRefinement (K := K))

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
