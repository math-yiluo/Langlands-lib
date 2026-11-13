import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology
import Langlands.Sheaf.Equivariant.TwistedRepCohomology

/-!
# The action of `G` on `H^q(X, b^*F)` and `H^q_c(X, b^*F)` for étale `G`-sheaves

Let `G` act on an analytic space `X` and let `F` be an étale `G`-sheaf of modules. This module
makes `H^q(X, b^*F)` and `H^q_c(X, b^*F)` into representations of `G`, the objects of
Berkovich's Corollary 1.5.2(i) and Theorem 1.6.1(ii). They are the constructions of
`TwistedRepCohomology` for the étale site, applied to the inclusion of étale `G`-sheaves into
sheaves on the twisted étale site. Coproducts of modules indexed by `G` exist and are exact
since `G` is small. The action is given both as a representation-valued functor with an
isomorphism of its underlying modules to `H^q(X, b^*F)` (resp. `H^q_c(X, b^*F)`), and as a
representation on the module `H^q(X, b^*F)` (resp. `H^q_c(X, b^*F)`) itself. That this
action is smooth is not proved.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Global

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]

/-- `H^q(X, b^*F)` for étale `G`-sheaves of modules, as representations of `G`: the right
derived functors of the global sections representation on the twisted étale site, applied to
the inclusion of étale `G`-sheaves. -/
def etaleRestrictionCohomologyRep (q : ℕ) :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      Rep.{max u (v + 1) uL} R G :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedEtale_enoughInjectives.{u, v, uL} X ρ R
  (distinguishedLiftSystem ρ).smoothSheafInclusion _ _ ⋙
    sheafGlobalRepDerived (etaleTopology X) R q

/-- The module underlying `etaleRestrictionCohomologyRep ρ R q` is `H^q(X, b^*F)`. -/
def etaleRestrictionCohomologyForgetIso (q : ℕ) :
    etaleRestrictionCohomologyRep.{u, v, uL} ρ R q ⋙
        forget₂ (Rep.{max u (v + 1) uL} R G) (ModuleCat.{max u (v + 1) uL} R) ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCohomology.{u, v, uL} X R q :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL} (G := G) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uL} (G := G) R
  Functor.isoWhiskerLeft ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)
    (restrictionGlobalCohomologyIso (etaleTopology X) R q)

/-- The canonical action of `G` on `H^q(X, b^*F)` for an étale `G`-sheaf `F`: the action on
`etaleRestrictionCohomologyRep ρ R q`, transported along
`etaleRestrictionCohomologyForgetIso`. -/
def etaleRestrictionCohomologyAction (q : ℕ) (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Representation R G ((etaleCohomology.{u, v, uL} X R q).obj
      ((etaleGSheafRestriction.{u, v, uL} ρ R).obj F)) :=
  (LinearEquiv.conjAlgEquiv R
    ((etaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).toLinearEquiv).toMonoidHom.comp
    ((etaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F).ρ

/-- The isomorphism `etaleRestrictionCohomologyForgetIso` intertwines the two actions. -/
theorem etaleRestrictionCohomologyAction_apply (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (g : G)
    (x : (etaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F) :
    etaleRestrictionCohomologyAction.{u, v, uL} ρ R q F g
        (((etaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).hom x) =
      ((etaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).hom
        (((etaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F).ρ g x) := by
  let e := ((etaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).toLinearEquiv
  change e ((((etaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F).ρ g) (e.symm (e x))) = e _
  rw [LinearEquiv.symm_apply_apply]

end Global

section Compact

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]

/-- `H^q_c(X, b^*F)` for étale `G`-sheaves of modules, with supports in the `L`-valued points,
as representations of `G`: the right derived functors of the compactly supported global
sections representation on the twisted étale site, applied to the inclusion of étale
`G`-sheaves. -/
def etaleRestrictionCompactCohomologyRep (q : ℕ) :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      Rep.{max u (v + 1) uL} R G :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedEtale_enoughInjectives.{u, v, uL} X ρ R
  (distinguishedLiftSystem ρ).smoothSheafInclusion _ _ ⋙
    sheafCompactRepDerived (etaleTopology X) R (EtaleSite.pointEquivariance L ρ h) q

/-- The module underlying `etaleRestrictionCompactCohomologyRep L ρ h R q` is
`H^q_c(X, b^*F)`. -/
def etaleRestrictionCompactCohomologyForgetIso (q : ℕ) :
    etaleRestrictionCompactCohomologyRep L ρ h R q ⋙
        forget₂ (Rep.{max u (v + 1) uL} R G) (ModuleCat.{max u (v + 1) uL} R) ≅
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCompactCohomology L h R q :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL} (G := G) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uL} (G := G) R
  Functor.isoWhiskerLeft ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)
    (restrictionCompactCohomologyIso (etaleTopology X) R (EtaleSite.pointEquivariance L ρ h) q)

/-- The canonical action of `G` on `H^q_c(X, b^*F)` for an étale `G`-sheaf `F` (Berkovich,
Corollary 1.5.2(i)): the action on `etaleRestrictionCompactCohomologyRep L ρ h R q`,
transported along `etaleRestrictionCompactCohomologyForgetIso`. -/
def etaleRestrictionCompactCohomologyAction (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Representation R G ((etaleCompactCohomology L h R q).obj
      ((etaleGSheafRestriction.{u, v, uL} ρ R).obj F)) :=
  (LinearEquiv.conjAlgEquiv R
    ((etaleRestrictionCompactCohomologyForgetIso L ρ h R q).app F).toLinearEquiv).toMonoidHom.comp
    ((etaleRestrictionCompactCohomologyRep L ρ h R q).obj F).ρ

/-- The isomorphism `etaleRestrictionCompactCohomologyForgetIso` intertwines the two
actions. -/
theorem etaleRestrictionCompactCohomologyAction_apply (q : ℕ)
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (g : G)
    (x : (etaleRestrictionCompactCohomologyRep L ρ h R q).obj F) :
    etaleRestrictionCompactCohomologyAction L ρ h R q F g
        (((etaleRestrictionCompactCohomologyForgetIso L ρ h R q).app F).hom x) =
      ((etaleRestrictionCompactCohomologyForgetIso L ρ h R q).app F).hom
        (((etaleRestrictionCompactCohomologyRep L ρ h R q).obj F).ρ g x) := by
  let e := ((etaleRestrictionCompactCohomologyForgetIso L ρ h R q).app F).toLinearEquiv
  change e ((((etaleRestrictionCompactCohomologyRep L ρ h R q).obj F).ρ g) (e.symm (e x))) = e _
  rw [LinearEquiv.symm_apply_apply]

end Compact

end Langlands.Sheaf.Equivariant.Analytic
