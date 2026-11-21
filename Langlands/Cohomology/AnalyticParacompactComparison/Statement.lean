import Mathlib.Topology.Compactness.Paracompact
import Langlands.Cohomology.ExactBaseChange
import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology

/-!
# Deriving ordinary sections of restricted analytic `G`-sheaves

Berkovich, Theorem 1.6.1(i), on both analytic sites. The comparison is from the
right derived functor of `F ↦ Γ(X, b^*F)` on equivariant sheaves to ordinary
cohomology after restriction. Neither smooth sections nor invariant sections
are used here.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology.AnalyticParacompactComparison

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable (ρ : G →* Aut X) (R : Type (max u (v + 1) uL)) [CommRing R]

section Etale

variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- `R^q(Γ(X, b^*(-))) ⟶ H^q(X, b^*(-))` for étale `G`-sheaves. This is
    the composite comparison along the exact functor `b^*`. -/
def etaleRestrictedSectionsComparison (q : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
    (etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleSections.{u, v, uL} X R).rightDerived q ⟶
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCohomology.{u, v, uL} X R q :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := etaleGSheafRestriction_preservesFiniteLimits.{u, v, uL} ρ R
  haveI := etaleGSheafRestriction_preservesFiniteColimits.{u, v, uL} ρ R
  ExactBaseChange.compComparisonNatTrans (etaleGSheafRestriction.{u, v, uL} ρ R)
    (etaleSections.{u, v, uL} X R) q

/-- Berkovich, Theorem 1.6.1(i), étale case: on a paracompact Hausdorff
    analytic `G`-space the comparison is a natural isomorphism in every degree. -/
def AnalyticEtaleParacompactComparisonStatement [IsTopologicalGroup G] : Prop :=
  T2Space (localizedSpaceFunctor.obj X) → ParacompactSpace (localizedSpaceFunctor.obj X) →
    IsContinuousAction ρ → ∀ q : ℕ, IsIso (etaleRestrictedSectionsComparison.{u, v, uL} ρ R q)

end Etale

section QuasiEtale

variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- `R^q(Γ(X, b^*(-))) ⟶ H^q(X, b^*(-))` for quasi-étale `G`-sheaves.
    This is the composite comparison along the exact functor `b^*`. -/
def quasiEtaleRestrictedSectionsComparison (q : ℕ) :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
    haveI := quasiEtaleGSheafRestriction_additive.{u, v, uL} ρ R
    (quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙
      quasiEtaleSections.{u, v, uL} X R).rightDerived q ⟶
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ quasiEtaleCohomology.{u, v, uL} X R q :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := quasiEtaleGSheafRestriction_additive.{u, v, uL} ρ R
  haveI := quasiEtaleGSheafRestriction_preservesFiniteLimits.{u, v, uL} ρ R
  haveI := quasiEtaleGSheafRestriction_preservesFiniteColimits.{u, v, uL} ρ R
  ExactBaseChange.compComparisonNatTrans (quasiEtaleGSheafRestriction.{u, v, uL} ρ R)
    (quasiEtaleSections.{u, v, uL} X R) q

/-- Berkovich, Theorem 1.6.1(i), quasi-étale case: on a paracompact Hausdorff
    analytic `G`-space the comparison is a natural isomorphism in every degree. -/
def AnalyticQuasiEtaleParacompactComparisonStatement [IsTopologicalGroup G] : Prop :=
  T2Space (localizedSpaceFunctor.obj X) → ParacompactSpace (localizedSpaceFunctor.obj X) →
    IsContinuousAction ρ →
      ∀ q : ℕ, IsIso (quasiEtaleRestrictedSectionsComparison.{u, v, uL} ρ R q)

end QuasiEtale

end Langlands.Cohomology.AnalyticParacompactComparison
