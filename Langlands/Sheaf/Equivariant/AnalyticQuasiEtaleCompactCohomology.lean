import Langlands.Sheaf.Equivariant.AnalyticCompactSupport
import Langlands.Geometry.Analytic.OverSitePoints
import Langlands.Cohomology.DiscreteSheafDerivedComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives

/-!
# Compactly supported cohomology of quasi-étale `G`-sheaves on analytic spaces

Let `G` act on an analytic space `X`. The quasi-étale site of `X` and the twisted
quasi-étale site are essentially small in the universe of the modules used for
compactly supported sections, so module sheaves on them have sheafification and
enough injectives. If every `L`-valued point of `X` satisfies the point axioms of
the quasi-étale site, the general construction of `TwistedCompactSupport` gives the
compactly supported global sections `Γ_{c,X{G}}` on quasi-étale `G`-sheaves, and,
given finite equivariant refinements of coverings of compact objects, their right
derived functors `H^q_c(X{G}, F)` and the complex `RΓ_c(X{G}, F)`.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport

universe u v uL z w'

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Size

variable (X : LocalizedCategory.{u, v, v} (K := K))

/-- The quasi-étale site of `X` is locally small at the universe `max u (v + 1) uL`. -/
theorem quasiEtaleSite_locallySmall_points :
    LocallySmall.{max u (v + 1) uL} (QuasiEtaleSite X) where
  hom_small U V := small_lift.{max u (v + 1), uL, max u (v + 1)} (U ⟶ V)

/-- The quasi-étale site of `X` is essentially small at the universe
`max u (v + 1) uL`. -/
theorem quasiEtaleSite_essentiallySmall_points :
    EssentiallySmall.{max u (v + 1) uL} (QuasiEtaleSite X) :=
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI : Small.{max u (v + 1) uL} (QuasiEtaleSite X) :=
    small_lift.{max u (v + 1), uL, max u (v + 1)} _
  essentiallySmall_of_small_of_locallySmall _

variable {G : Type z} [Group G] (ρ : G →* Aut X)

/-- If `G` is small at the universe `max u (v + 1) uL`, the twisted quasi-étale site
is locally small at that universe: a twisted morphism is determined by its twist
and its underlying arrow. -/
theorem twistedQuasiEtale_locallySmall_points [Small.{max u (v + 1) uL} G] :
    LocallySmall.{max u (v + 1) uL} (TwistedOver (quasiEtale (K := K)) ρ) where
  hom_small U V := by
    have : Small.{max u (v + 1) uL} (U.obj.left ⟶ V.obj.left) :=
      small_lift.{max u (v + 1), uL, max u (v + 1)} _
    exact small_of_injective (f := fun f : TwistedOver.Hom U V => (f.twist, f.left))
      fun f g hfg => TwistedOver.Hom.ext (congrArg Prod.fst hfg) (congrArg Prod.snd hfg)

/-- If `G` is small at the universe `max u (v + 1) uL`, the twisted quasi-étale site
is essentially small at that universe. -/
theorem twistedQuasiEtale_essentiallySmall_points [Small.{max u (v + 1) uL} G] :
    EssentiallySmall.{max u (v + 1) uL} (TwistedOver (quasiEtale (K := K)) ρ) :=
  haveI := twistedQuasiEtale_locallySmall_points.{u, v, uL} X ρ
  haveI : Small.{max u (v + 1) uL} (TwistedOver (quasiEtale (K := K)) ρ) :=
    small_lift.{max u (v + 1), uL, max u (v + 1)} _
  essentiallySmall_of_small_of_locallySmall _

variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Module sheaves on the quasi-étale site of `X` have sheafification. -/
theorem quasiEtale_hasSheafify :
    HasSheafify (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := quasiEtaleSite_essentiallySmall_points.{u, v, uL} X
  hasSheafifyEssentiallySmallSite _ _

/-- Module sheaves on the twisted quasi-étale site have sheafification. -/
theorem twistedQuasiEtale_hasSheafify [Small.{max u (v + 1) uL} G] :
    HasSheafify (twistedQuasiEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedQuasiEtale_essentiallySmall_points.{u, v, uL} X ρ
  hasSheafifyEssentiallySmallSite _ _

/-- Module sheaves on the twisted quasi-étale site form a Grothendieck abelian
category, so they have enough injectives. -/
theorem twistedQuasiEtale_enoughInjectives [Small.{max u (v + 1) uL} G] :
    EnoughInjectives (Sheaf (twistedQuasiEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R)) :=
  haveI := twistedQuasiEtale_essentiallySmall_points.{u, v, uL} X ρ
  haveI := twistedQuasiEtale_locallySmall_points.{u, v, uL} X ρ
  haveI : ∀ Y : (TwistedOver (quasiEtale (K := K)) ρ)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Y (equivSmallModel.{max u (v + 1) uL}
        (TwistedOver (quasiEtale (K := K)) ρ)).inverse.op) (ModuleCat.{max u (v + 1) uL} R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL} _ _
  haveI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u (v + 1) uL}
    (twistedQuasiEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R)
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  IsGrothendieckAbelian.enoughInjectives

end Size

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]

section Support

variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)

/-- The family of points of the quasi-étale site of `X` given by its `L`-valued points. -/
abbrev quasiEtalePoints (x : (localizedFieldPointFunctor L).obj X) :
    (quasiEtaleTopology X).Point.{max u (v + 1) uL} :=
  QuasiEtaleSite.toPoint L x (h x)

/-- A section of a module presheaf on the quasi-étale site is compactly supported for
the `L`-valued points exactly when the image of its support in `|X|` lies in a compact
set of underlying points of `L`-valued points. -/
theorem isCompactlySupported_quasiEtalePoints_iff {R : Type (max u (v + 1) uL)} [CommRing R]
    {F : (QuasiEtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R} {U : QuasiEtaleSite X}
    (s : F.obj (op U)) :
    letI := pointTopology L X
    haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
    IsCompactlySupported (quasiEtalePoints L h) F s ↔
      ∃ C : Set (localizedSpaceFunctor.obj X), IsCompact C ∧
        C ⊆ Set.range (pointProjection L X) ∧
          pointProjection L X '' support (quasiEtalePoints L h) F s ⊆ C :=
  exists_isCompact_superset_iff L _

end Support

section CompactSections

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Compactly supported global sections of module sheaves on the twisted quasi-étale
site of `X`, as representations of `G`; supports are taken in the `L`-valued points. -/
def quasiEtaleCompactSectionsRep :
    Sheaf (twistedQuasiEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R) ⥤
      Rep.{max u (v + 1) uL} R G :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  sheafCompactSectionsRep (quasiEtaleTopology X) R (QuasiEtaleSite.pointEquivariance L ρ h)

instance quasiEtaleCompactSectionsRep_additive :
    (quasiEtaleCompactSectionsRep L ρ h R).Additive :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  inferInstanceAs (sheafCompactSectionsRep (quasiEtaleTopology X) R
    (QuasiEtaleSite.pointEquivariance L ρ h)).Additive

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Berkovich's `Γ_{c,X{G}}` on the twisted quasi-étale site: the smooth part of the
compactly supported global sections. -/
def quasiEtaleCompactSectionsSmooth :
    Sheaf (twistedQuasiEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  quasiEtaleCompactSectionsRep L ρ h R ⋙ SmoothRep.smoothPartFunctor R G

instance quasiEtaleCompactSectionsSmooth_additive :
    (quasiEtaleCompactSectionsSmooth L ρ h R).Additive where
  map_add := rfl

/-- `Γ_{c,X{G}}` on Berkovich's quasi-étale `G`-sheaves. It is the functor
`discreteCompactSections` of `TwistedCompactSupport` for the lifts on compact
quasi-étale objects. -/
def quasiEtaleGSheafCompactSections :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  discreteCompactSections (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h)

/-- `Γ_{c,X{G}}` on quasi-étale `G`-sheaves is the inclusion into sheaves on the twisted
quasi-étale site followed by `quasiEtaleCompactSectionsSmooth`. -/
theorem quasiEtaleGSheafCompactSections_eq :
    quasiEtaleGSheafCompactSections L ρ h R =
      (compactLiftSystem ρ).discreteSheafInclusion _ _ ⋙
        quasiEtaleCompactSectionsSmooth L ρ h R :=
  rfl

instance quasiEtaleGSheafCompactSections_additive :
    (quasiEtaleGSheafCompactSections L ρ h R).Additive := by
  rw [quasiEtaleGSheafCompactSections_eq]
  infer_instance

end CompactSections

section Derived

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- Berkovich's `H^q_c(X{G}, F)` for quasi-étale `G`-sheaves of modules: the right
derived functors of `Γ_{c,X{G}}` on `T_G(X_qét)`, computed with injective resolutions
among quasi-étale `G`-sheaves. Sheafification and enough injectives are proved in
this module; the finite equivariant refinements are a hypothesis. -/
def quasiEtaleGSheafCompactCohomology (q : ℕ) :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  discreteCompactDerived (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h) q

/-- In degree zero, `H^0_c(X{G}, F)` is `Γ_{c,X{G}}(F)`. -/
def quasiEtaleGSheafCompactCohomologyZeroIso :
    quasiEtaleGSheafCompactCohomology L ρ h R 0 ≅ quasiEtaleGSheafCompactSections L ρ h R :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  discreteCompactDerivedZeroIso (quasiEtaleTopology X) (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h)

/-- `H^q_c(X{G}, -)` vanishes in positive degrees on injective quasi-étale
`G`-sheaves. -/
theorem isZero_quasiEtaleGSheafCompactCohomology_succ_of_injective
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective F] (q : ℕ) :
    IsZero ((quasiEtaleGSheafCompactCohomology L ρ h R (q + 1)).obj F) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  isZero_discreteCompactDerived_succ_of_injective (quasiEtaleTopology X)
    (compactLiftSystem ρ) (QuasiEtaleSite.pointEquivariance L ρ h) F q

variable [HasDerivedCategory.{w'} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]

/-- The complex `RΓ_c(X{G}, F)` in the bounded below derived category of smooth
representations of `G`: `Γ_{c,X{G}}` derived with injective resolutions among
quasi-étale `G`-sheaves. The derived category of quasi-étale `G`-sheaves used inside
is Mathlib's standard one; the resulting functor does not depend on it. -/
def quasiEtaleGSheafCompactComplex :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  Cohomology.DiscreteSheafDerivedComplex.compactComplex (quasiEtaleTopology X) R
    (compactLiftSystem ρ) (QuasiEtaleSite.pointEquivariance L ρ h)

/-- The cohomology of `RΓ_c(X{G}, F)` in degree `q` is `H^q_c(X{G}, F)`. -/
def quasiEtaleGSheafCompactComplexHomologyIso
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor
        (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) q).obj
        ((quasiEtaleGSheafCompactComplex L ρ h R).obj F) ≅
      (quasiEtaleGSheafCompactCohomology L ρ h R q).obj F :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  Cohomology.DiscreteSheafDerivedComplex.compactComplexHomologyIso (quasiEtaleTopology X) R
    (compactLiftSystem ρ) (QuasiEtaleSite.pointEquivariance L ρ h) F q

/-- `RΓ_c(X{G}, F)` has no cohomology in negative degrees. -/
theorem isZero_quasiEtaleGSheafCompactComplex_homology
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
        (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) n).obj
        ((quasiEtaleGSheafCompactComplex L ρ h R).obj F)) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  Cohomology.DiscreteSheafDerivedComplex.isZero_compactComplex_homology (quasiEtaleTopology X) R
    (compactLiftSystem ρ) (QuasiEtaleSite.pointEquivariance L ρ h) F hn

end Derived

end Langlands.Sheaf.Equivariant.Analytic
