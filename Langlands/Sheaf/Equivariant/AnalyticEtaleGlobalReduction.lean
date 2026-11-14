import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology
import Langlands.Cohomology.ExactBaseChange.InjectiveAcyclic

/-!
# Analytic étale global comparison from injective acyclicity

The published comparison is invertible if its degree-zero inclusion is invertible
and restriction sends injective étale `G`-sheaves to globally acyclic sheaves.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G]
variable [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- A degree-zero isomorphism and acyclicity of restrictions of injective
étale `G`-sheaves make every published global comparison map invertible. -/
theorem isIso_etaleComparison_of_injective_acyclic
    [IsIso (etaleGlobalInclusion.{u, v, uL} ρ R)]
    (hacyclic :
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      ∀ (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I] (r : ℕ),
        IsZero ((etaleCohomology.{u, v, uL} X R (r + 1)).obj
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I)))
    (q : ℕ) : IsIso (etaleComparison.{u, v, uL} ρ R q) := by
  have := etale_hasSheafify.{u, v, uL} X R
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  have := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  have := etale_enoughInjectives.{u, v, uL} X R
  have := etaleGSheafSections_preservesFiniteLimits.{u, v, uL} ρ R
  have := etaleGSheafRestriction_preservesFiniteLimits.{u, v, uL} ρ R
  have := etaleGSheafRestriction_preservesFiniteColimits.{u, v, uL} ρ R
  exact ExactBaseChange.isIso_baseChangeNatTrans_of_injective_acyclic
    (etaleGlobalInclusion.{u, v, uL} ρ R) hacyclic q

/-- The natural isomorphism whose forward map is `etaleComparison`, under
degree-zero invertibility and acyclicity of restrictions of injectives. -/
def etaleComparisonIsoOfInjectiveAcyclic
    [IsIso (etaleGlobalInclusion.{u, v, uL} ρ R)]
    (hacyclic :
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      ∀ (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I] (r : ℕ),
        IsZero ((etaleCohomology.{u, v, uL} X R (r + 1)).obj
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I)))
    (q : ℕ) :
    etaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCohomology.{u, v, uL} X R q := by
  haveI := isIso_etaleComparison_of_injective_acyclic ρ R hacyclic q
  exact asIso (etaleComparison.{u, v, uL} ρ R q)

end Langlands.Sheaf.Equivariant.Analytic
