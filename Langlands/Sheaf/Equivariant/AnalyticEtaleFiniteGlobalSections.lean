import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology
import Langlands.Sheaf.Equivariant.TwistedFiniteGlobalInclusion

/-!
# Étale global sections under finite base subcovers

The distinguished local-action system consists of lifted actions. Therefore the
finite-base descent theorem makes the canonical inclusion of smooth global
sections of an étale `G`-sheaf an isomorphism.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Finite subcovers at the twisted base make the canonical global-section
inclusion of étale `G`-sheaves an isomorphism. -/
theorem isIso_etaleGlobalInclusion_of_finiteBaseSubcovers
    (hfin : HasFiniteBaseSubcovers (twistedEtaleTopology ρ)) :
    IsIso (etaleGlobalInclusion.{u, v, uL} ρ R) := by
  exact isIso_exactGlobalInclusion_of_locallyDiscrete (J := etaleTopology X) (R := R)
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) hfin
    (distinguishedLiftSystem ρ) (isLiftSystem_liftSystem _) (fun F => F.property)

/-- Under finite subcovers at the twisted base, smooth global sections of an
étale `G`-sheaf coincide naturally with all global sections of its restriction. -/
def etaleFiniteGlobalSectionsIso
    (hfin : HasFiniteBaseSubcovers (twistedEtaleTopology ρ)) :
    etaleGSheafSections.{u, v, uL} ρ R ⋙ smoothForget R G ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleSections.{u, v, uL} X R :=
  haveI := isIso_etaleGlobalInclusion_of_finiteBaseSubcovers ρ R hfin
  asIso (etaleGlobalInclusion.{u, v, uL} ρ R)

/-- The forward map is the canonical smooth-global-section inclusion. -/
theorem etaleFiniteGlobalSectionsIso_hom
    (hfin : HasFiniteBaseSubcovers (twistedEtaleTopology ρ)) :
    (etaleFiniteGlobalSectionsIso.{u, v, uL} ρ R hfin).hom =
      etaleGlobalInclusion.{u, v, uL} ρ R :=
  rfl

end Langlands.Sheaf.Equivariant.Analytic
