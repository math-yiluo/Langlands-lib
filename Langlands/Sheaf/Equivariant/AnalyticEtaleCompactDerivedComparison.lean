import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison
import Langlands.Cohomology.ExactBaseChange.InjectiveAcyclic

/-!
# Compact étale comparison from degree zero and restricted-injective acyclicity

This conditional construction specializes exact derived base change to the actual
compact-support comparison. The degree-zero isomorphism and the vanishing for restricted
injectives remain explicit premises.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Cohomology
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- A degree-zero compact comparison isomorphism and compact acyclicity of restricted
injectives make the actual comparison an isomorphism in every degree. -/
theorem isIso_etaleCompactComparison_of_injective_acyclic
    (hzero : IsIso (etaleCompactInclusion L ρ h R))
    (hacyclic :
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      ∀ (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I] (r : ℕ),
        IsZero ((etaleCompactCohomology L h R (r + 1)).obj
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I))) (q : ℕ) :
    IsIso (etaleCompactComparison L ρ h R q) := by
  let := pointTopology L X
  let := EtaleSite.pointAction L ρ
  have := continuousConstSMul_pointAction L ρ
  have := etaleSite_locallySmall_points.{u, v, uL} X
  have := etale_hasSheafify.{u, v, uL} X R
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  have := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  have := etale_enoughInjectives.{u, v, uL} X R
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  have := etaleGSheafCompactSections_preservesFiniteLimits L ρ h R
  have : PreservesFiniteLimits (etaleCompactSections L h R) :=
    inferInstanceAs (PreservesFiniteLimits
      (sheafCompactSections (etaleTopology X) (etalePoints L h) R (etaleSelf X)))
  have := etaleGSheafRestriction_preservesFiniteLimits.{u, v, uL} ρ R
  have := etaleGSheafRestriction_preservesFiniteColimits.{u, v, uL} ρ R
  have := hzero
  exact ExactBaseChange.isIso_baseChangeNatTrans_of_injective_acyclic
    (etaleCompactInclusion L ρ h R) hacyclic q

/-- The natural compact étale comparison isomorphism under the explicit degree-zero
and restricted-injective acyclicity premises. Its forward map is `etaleCompactComparison`. -/
def etaleCompactComparisonIsoOfInjectiveAcyclic
    (hzero : IsIso (etaleCompactInclusion L ρ h R))
    (hacyclic :
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      ∀ (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I] (r : ℕ),
        IsZero ((etaleCompactCohomology L h R (r + 1)).obj
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I))) (q : ℕ) :
    etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCompactCohomology L h R q :=
  haveI := isIso_etaleCompactComparison_of_injective_acyclic L ρ h R hzero hacyclic q
  asIso (etaleCompactComparison L ρ h R q)

/-- The constructed isomorphism uses the existing canonical comparison as its forward map. -/
theorem etaleCompactComparisonIsoOfInjectiveAcyclic_hom
    (hzero : IsIso (etaleCompactInclusion L ρ h R))
    (hacyclic :
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      ∀ (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I] (r : ℕ),
        IsZero ((etaleCompactCohomology L h R (r + 1)).obj
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I))) (q : ℕ) :
    (etaleCompactComparisonIsoOfInjectiveAcyclic L ρ h R hzero hacyclic q).hom =
      etaleCompactComparison L ρ h R q := rfl

end Langlands.Sheaf.Equivariant.Analytic
