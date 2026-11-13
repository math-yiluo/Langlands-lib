import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology
import Langlands.Sheaf.Equivariant.TwistedRepCohomology

/-!
# The action of `G` on `H^q(X, b^*F)` and `H^q_c(X, b^*F)` for quasi-étale `G`-sheaves

Let `G` act on an analytic space `X` and let `F` be a quasi-étale `G`-sheaf of modules. This
module makes `H^q(X, b^*F)` and `H^q_c(X, b^*F)` into representations of `G`, the objects of
Berkovich's Corollary 1.5.2(i) and Theorem 1.6.1(ii). They are the constructions of
`TwistedRepCohomology` for the quasi-étale site, applied to the inclusion of quasi-étale
`G`-sheaves into sheaves on the twisted quasi-étale site. Coproducts of modules indexed by `G`
exist and are exact since `G` is small. The action is given both as a representation-valued
functor with an isomorphism of its underlying modules to `H^q(X, b^*F)` (resp.
`H^q_c(X, b^*F)`), and as a representation on the module `H^q(X, b^*F)` (resp.
`H^q_c(X, b^*F)`) itself. That this action is smooth is not proved.
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

/-- `H^q(X, b^*F)` for quasi-étale `G`-sheaves of modules, as representations of `G`: the
right derived functors of the global sections representation on the twisted quasi-étale site,
applied to the inclusion of quasi-étale `G`-sheaves. -/
def quasiEtaleRestrictionCohomologyRep (q : ℕ) :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      Rep.{max u (v + 1) uL} R G :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  (compactLiftSystem ρ).discreteSheafInclusion _ _ ⋙
    sheafGlobalRepDerived (quasiEtaleTopology X) R q

/-- The module underlying `quasiEtaleRestrictionCohomologyRep ρ R q` is `H^q(X, b^*F)`. -/
def quasiEtaleRestrictionCohomologyForgetIso (q : ℕ) :
    quasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q ⋙
        forget₂ (Rep.{max u (v + 1) uL} R G) (ModuleCat.{max u (v + 1) uL} R) ≅
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ quasiEtaleCohomology.{u, v, uL} X R q :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL} (G := G) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uL} (G := G) R
  Functor.isoWhiskerLeft ((compactLiftSystem ρ).discreteSheafInclusion _ _)
    (restrictionGlobalCohomologyIso (quasiEtaleTopology X) R q)

/-- The canonical action of `G` on `H^q(X, b^*F)` for a quasi-étale `G`-sheaf `F`: the action
on `quasiEtaleRestrictionCohomologyRep ρ R q`, transported along
`quasiEtaleRestrictionCohomologyForgetIso`. -/
def quasiEtaleRestrictionCohomologyAction (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Representation R G ((quasiEtaleCohomology.{u, v, uL} X R q).obj
      ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj F)) :=
  (LinearEquiv.conjAlgEquiv R
    ((quasiEtaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app
      F).toLinearEquiv).toMonoidHom.comp
    ((quasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F).ρ

/-- The isomorphism `quasiEtaleRestrictionCohomologyForgetIso` intertwines the two actions. -/
theorem quasiEtaleRestrictionCohomologyAction_apply (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (g : G)
    (x : (quasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F) :
    quasiEtaleRestrictionCohomologyAction.{u, v, uL} ρ R q F g
        (((quasiEtaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).hom x) =
      ((quasiEtaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).hom
        (((quasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F).ρ g x) := by
  let e := ((quasiEtaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).toLinearEquiv
  change e ((((quasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F).ρ g)
    (e.symm (e x))) = e _
  rw [LinearEquiv.symm_apply_apply]

end Global

section Compact

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]

/-- `H^q_c(X, b^*F)` for quasi-étale `G`-sheaves of modules, with supports in the `L`-valued
points, as representations of `G`: the right derived functors of the compactly supported
global sections representation on the twisted quasi-étale site, applied to the inclusion of
quasi-étale `G`-sheaves. -/
def quasiEtaleRestrictionCompactCohomologyRep (q : ℕ) :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      Rep.{max u (v + 1) uL} R G :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  (compactLiftSystem ρ).discreteSheafInclusion _ _ ⋙
    sheafCompactRepDerived (quasiEtaleTopology X) R (QuasiEtaleSite.pointEquivariance L ρ h) q

/-- The module underlying `quasiEtaleRestrictionCompactCohomologyRep L ρ h R q` is
`H^q_c(X, b^*F)`. -/
def quasiEtaleRestrictionCompactCohomologyForgetIso (q : ℕ) :
    quasiEtaleRestrictionCompactCohomologyRep L ρ h R q ⋙
        forget₂ (Rep.{max u (v + 1) uL} R G) (ModuleCat.{max u (v + 1) uL} R) ≅
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ quasiEtaleCompactCohomology L h R q :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL} (G := G) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uL} (G := G) R
  Functor.isoWhiskerLeft ((compactLiftSystem ρ).discreteSheafInclusion _ _)
    (restrictionCompactCohomologyIso (quasiEtaleTopology X) R
      (QuasiEtaleSite.pointEquivariance L ρ h) q)

/-- The canonical action of `G` on `H^q_c(X, b^*F)` for a quasi-étale `G`-sheaf `F`
(Berkovich, Corollary 1.5.2(i)): the action on
`quasiEtaleRestrictionCompactCohomologyRep L ρ h R q`, transported along
`quasiEtaleRestrictionCompactCohomologyForgetIso`. -/
def quasiEtaleRestrictionCompactCohomologyAction (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Representation R G ((quasiEtaleCompactCohomology L h R q).obj
      ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj F)) :=
  (LinearEquiv.conjAlgEquiv R
    ((quasiEtaleRestrictionCompactCohomologyForgetIso L ρ h R q).app
      F).toLinearEquiv).toMonoidHom.comp
    ((quasiEtaleRestrictionCompactCohomologyRep L ρ h R q).obj F).ρ

/-- The isomorphism `quasiEtaleRestrictionCompactCohomologyForgetIso` intertwines the two
actions. -/
theorem quasiEtaleRestrictionCompactCohomologyAction_apply (q : ℕ)
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (g : G)
    (x : (quasiEtaleRestrictionCompactCohomologyRep L ρ h R q).obj F) :
    quasiEtaleRestrictionCompactCohomologyAction L ρ h R q F g
        (((quasiEtaleRestrictionCompactCohomologyForgetIso L ρ h R q).app F).hom x) =
      ((quasiEtaleRestrictionCompactCohomologyForgetIso L ρ h R q).app F).hom
        (((quasiEtaleRestrictionCompactCohomologyRep L ρ h R q).obj F).ρ g x) := by
  let e := ((quasiEtaleRestrictionCompactCohomologyForgetIso L ρ h R q).app F).toLinearEquiv
  change e ((((quasiEtaleRestrictionCompactCohomologyRep L ρ h R q).obj F).ρ g)
    (e.symm (e x))) = e _
  rw [LinearEquiv.symm_apply_apply]

end Compact

end Langlands.Sheaf.Equivariant.Analytic
