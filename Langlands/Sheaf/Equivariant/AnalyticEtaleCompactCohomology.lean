import Langlands.Sheaf.Equivariant.AnalyticCompactSupport
import Langlands.Sheaf.Equivariant.LocalActionSmoothPart
import Langlands.Cohomology.DerivedPlus
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Compactly supported cohomology of étale `G`-sheaves on analytic spaces

Let `G` act on an analytic space `X`. The étale site of `X` and the twisted étale
site are essentially small in the universe of the modules used for compactly
supported sections, so module sheaves on them have sheafification and enough
injectives. Assume that the lifts of the action to distinguished étale objects
have admissible refinements on the twisted étale site. Then Berkovich's étale
`G`-sheaves of modules form an abelian category with enough injectives, and the
compactly supported global sections `Γ_{c,X{G}}` have right derived functors
`H^q_c(X{G}, F)` and a derived complex `RΓ_c(X{G}, F)`.
-/

noncomputable section

universe w u v uL z w'

namespace Langlands.Sheaf.Equivariant.LocalActionSystem

open CategoryTheory

variable {T : Type*} [Category T] {G : Type*} [Group G] [TopologicalSpace G]
variable (L : LocalActionSystem T G) (J : GrothendieckTopology T)
variable (R : Type*) [CommRing R]

/-- The inclusion of locally discrete module sheaves is additive. -/
instance smoothSheafInclusion_additive :
    (L.smoothSheafInclusion (ModuleCat.{w} R) J).Additive :=
  inferInstanceAs (L.smoothSheafProperty (ModuleCat.{w} R) J).ι.Additive

end Langlands.Sheaf.Equivariant.LocalActionSystem

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Size

variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- The étale site of `X` is essentially small at the universe `max u (v + 1) uL`. -/
theorem etaleSite_essentiallySmall_points :
    EssentiallySmall.{max u (v + 1) uL} (EtaleSite X) :=
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI : Small.{max u (v + 1) uL} (EtaleSite X) :=
    small_lift.{max u (v + 1), uL, max u (v + 1)} _
  essentiallySmall_of_small_of_locallySmall _

variable {G : Type z} [Group G] (ρ : G →* Aut X)

/-- If `G` is small at the universe `max u (v + 1) uL`, the twisted étale site is
locally small at that universe: a twisted morphism is determined by its twist and
its underlying arrow. -/
theorem twistedEtale_locallySmall_points [Small.{max u (v + 1) uL} G] :
    LocallySmall.{max u (v + 1) uL} (TwistedOver (etale (K := K)) ρ) where
  hom_small U V := by
    have : Small.{max u (v + 1) uL} (U.obj.left ⟶ V.obj.left) :=
      small_lift.{max u (v + 1), uL, max u (v + 1)} _
    exact small_of_injective (f := fun f : TwistedOver.Hom U V => (f.twist, f.left))
      fun f g hfg => TwistedOver.Hom.ext (congrArg Prod.fst hfg) (congrArg Prod.snd hfg)

/-- If `G` is small at the universe `max u (v + 1) uL`, the twisted étale site is
essentially small at that universe. -/
theorem twistedEtale_essentiallySmall_points [Small.{max u (v + 1) uL} G] :
    EssentiallySmall.{max u (v + 1) uL} (TwistedOver (etale (K := K)) ρ) :=
  haveI := twistedEtale_locallySmall_points.{u, v, uL} X ρ
  haveI : Small.{max u (v + 1) uL} (TwistedOver (etale (K := K)) ρ) :=
    small_lift.{max u (v + 1), uL, max u (v + 1)} _
  essentiallySmall_of_small_of_locallySmall _

variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Module sheaves on the étale site of `X` have sheafification. -/
theorem etale_hasSheafify :
    HasSheafify (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := etaleSite_essentiallySmall_points.{u, v, uL} X
  hasSheafifyEssentiallySmallSite _ _

/-- Module sheaves on the twisted étale site have sheafification. -/
theorem twistedEtale_hasSheafify [Small.{max u (v + 1) uL} G] :
    HasSheafify (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedEtale_essentiallySmall_points.{u, v, uL} X ρ
  hasSheafifyEssentiallySmallSite _ _

/-- Module sheaves on the twisted étale site form a Grothendieck abelian category,
so they have enough injectives. -/
theorem twistedEtale_enoughInjectives [Small.{max u (v + 1) uL} G] :
    EnoughInjectives (Sheaf (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R)) :=
  haveI := twistedEtale_essentiallySmall_points.{u, v, uL} X ρ
  haveI := twistedEtale_locallySmall_points.{u, v, uL} X ρ
  haveI : ∀ Y : (TwistedOver (etale (K := K)) ρ)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Y (equivSmallModel.{max u (v + 1) uL}
        (TwistedOver (etale (K := K)) ρ)).inverse.op) (ModuleCat.{max u (v + 1) uL} R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL} _ _
  haveI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u (v + 1) uL}
    (twistedEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R)
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  IsGrothendieckAbelian.enoughInjectives

end Size

section GSheaves

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- Berkovich's étale `G`-sheaves of modules form an abelian category. -/
abbrev etaleGSheafAbelian : Abelian (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  LocalActionSystem.smoothSheaf_abelian _ _

/-- Berkovich's étale `G`-sheaves of modules have enough injectives. -/
theorem etaleGSheaf_enoughInjectives :
    EnoughInjectives (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedEtale_enoughInjectives.{u, v, uL} X ρ R
  LocalActionSystem.smoothSheaf_enoughInjectives _ _

end GSheaves

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]

section Derived

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- `Γ_{c,X{G}}` on étale `G`-sheaves is the inclusion into sheaves on the twisted
étale site followed by `etaleCompactSectionsSmooth`. -/
theorem etaleGSheafCompactSections_eq :
    etaleGSheafCompactSections L ρ h R =
      (distinguishedLiftSystem ρ).smoothSheafInclusion _ _ ⋙
        etaleCompactSectionsSmooth L ρ h R :=
  rfl

instance etaleGSheafCompactSections_additive :
    (etaleGSheafCompactSections L ρ h R).Additive := by
  rw [etaleGSheafCompactSections_eq]
  infer_instance

variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- `Γ_{c,X{G}}` on étale `G`-sheaves is left exact. -/
theorem etaleGSheafCompactSections_preservesFiniteLimits :
    PreservesFiniteLimits (etaleGSheafCompactSections L ρ h R) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI : LocallySmall.{max u (v + 1) uL} (EtaleSite X) :=
    etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI : PreservesFiniteLimits (etaleCompactSectionsSmooth L ρ h R) :=
    inferInstanceAs (PreservesFiniteLimits (sheafCompactSectionsSmooth (etaleTopology X) R
      (EtaleSite.pointEquivariance L ρ h)))
  comp_preservesFiniteLimits _ _

/-- Berkovich's `H^q_c(X{G}, F)` for étale `G`-sheaves of modules: the right derived
functors of `Γ_{c,X{G}}` on `T_G(X_ét)`, computed with injective resolutions among
étale `G`-sheaves. Sheafification and enough injectives are proved; the admissible
refinements of the distinguished lift system are a hypothesis. -/
def etaleGSheafCompactCohomology (q : ℕ) :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  (etaleGSheafCompactSections L ρ h R).rightDerived q

/-- In degree zero, `H^0_c(X{G}, F)` is `Γ_{c,X{G}}(F)`. -/
def etaleGSheafCompactCohomologyZeroIso :
    etaleGSheafCompactCohomology L ρ h R 0 ≅ etaleGSheafCompactSections L ρ h R :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etaleGSheafCompactSections_preservesFiniteLimits.{u, v, uL} L ρ h R
  (etaleGSheafCompactSections L ρ h R).rightDerivedZeroIsoSelf

/-- `H^q_c(X{G}, F)` is computed by any injective resolution among étale
`G`-sheaves. -/
def etaleGSheafCompactCohomologyIso {F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)}
    (I : haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R; InjectiveResolution F) (q : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    (etaleGSheafCompactCohomology L ρ h R q).obj F ≅
      (HomologicalComplex.homologyFunctor
          (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) (ComplexShape.up ℕ) q).obj
        (((etaleGSheafCompactSections L ρ h R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  I.isoRightDerivedObj (etaleGSheafCompactSections L ρ h R) q

/-- `H^q_c(X{G}, -)` vanishes in positive degrees on injective étale `G`-sheaves. -/
theorem isZero_etaleGSheafCompactCohomology_succ_of_injective
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective F] (q : ℕ) :
    IsZero ((etaleGSheafCompactCohomology L ρ h R (q + 1)).obj F) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  (etaleGSheafCompactSections L ρ h R).isZero_rightDerived_obj_injective_succ q F

variable [HasDerivedCategory.{w'} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]

/-- The complex `RΓ_c(X{G}, F)` in the bounded below derived category of smooth
representations of `G`: `Γ_{c,X{G}}` derived with injective resolutions among étale
`G`-sheaves. The derived category of étale `G`-sheaves used inside is Mathlib's
standard one; the resulting functor does not depend on it up to isomorphism of
cohomology. -/
def etaleGSheafCompactComplex :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etaleGSheafCompactSections_preservesFiniteLimits.{u, v, uL} L ρ h R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  Cohomology.DerivedPlus.derivedComplex (etaleGSheafCompactSections L ρ h R)

/-- The cohomology of `RΓ_c(X{G}, F)` in degree `q` is `H^q_c(X{G}, F)`. -/
def etaleGSheafCompactComplexHomologyIso
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor
        (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) q).obj
        ((etaleGSheafCompactComplex L ρ h R).obj F) ≅
      (etaleGSheafCompactCohomology L ρ h R q).obj F :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etaleGSheafCompactSections_preservesFiniteLimits.{u, v, uL} L ρ h R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  Cohomology.DerivedPlus.homologyIso (etaleGSheafCompactSections L ρ h R)
    (injectiveResolution F) q

/-- `RΓ_c(X{G}, F)` has no cohomology in negative degrees. -/
theorem isZero_etaleGSheafCompactComplex_homology
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
        (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) n).obj
        ((etaleGSheafCompactComplex L ρ h R).obj F)) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etaleGSheafCompactSections_preservesFiniteLimits.{u, v, uL} L ρ h R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  Cohomology.DerivedPlus.isZero_homology_of_neg (etaleGSheafCompactSections L ρ h R) F hn

end Derived

end Langlands.Sheaf.Equivariant.Analytic
