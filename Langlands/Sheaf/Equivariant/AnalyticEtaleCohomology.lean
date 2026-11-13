import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison
import Langlands.Sheaf.Equivariant.TwistedExactGlobalComparison

/-!
# Cohomology of étale sheaves and étale `G`-sheaves

Let `G` act on an analytic space `X`. This module defines the cohomology `H^q(X, F)` of
module sheaves on the étale site of `X`, Berkovich's `H^q(X{G}, F)` of étale `G`-sheaves as
smooth representations of `G`, the cohomology `H^q(X(G), F)` of the invariant global
sections with its edge map to the invariants of `H^q(X{G}, F)`, and the comparison maps
`H^q(X{G}, F) → H^q(X, b^*F)` of Berkovich's Theorem 1.6.1(ii). These are the
constructions of `TwistedExactGlobalComparison` for the étale site, with the inclusion of
étale `G`-sheaves into sheaves on the twisted étale site. No family of points is involved.
That the comparison maps are isomorphisms is not proved.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Plain

variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Global sections `Γ(X, F)` of module sheaves on the étale site of `X`: the sections over
`X` itself. -/
def etaleSections :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  sheafSectionsModule (etaleTopology X) R (etaleSelf X)

instance etaleSections_additive : (etaleSections.{u, v, uL} X R).Additive :=
  inferInstanceAs (sheafSectionsModule (etaleTopology X) R (etaleSelf X)).Additive

/-- `Γ(X, -)` is left exact. -/
instance etaleSections_preservesFiniteLimits :
    PreservesFiniteLimits (etaleSections.{u, v, uL} X R) :=
  inferInstanceAs
    (PreservesFiniteLimits (sheafSectionsModule (etaleTopology X) R (etaleSelf X)))

/-- `H^q(X, F)` for module sheaves on the étale site of `X`: the right derived functors of
`Γ(X, -)`, computed with injective resolutions of module sheaves. Sheafification and enough
injectives are proved. -/
def etaleCohomology (q : ℕ) :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  sectionsDerived (etaleTopology X) R (etaleSelf X) q

/-- In degree zero, `H^0(X, F)` is `Γ(X, F)`. -/
def etaleCohomologyZeroIso :
    etaleCohomology.{u, v, uL} X R 0 ≅ etaleSections.{u, v, uL} X R :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  sectionsDerivedZeroIso (etaleTopology X) R (etaleSelf X)

/-- `H^{q+1}(X, F) = 0` for injective `F`. -/
theorem isZero_etaleCohomology_succ_of_injective
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) [Injective F] (q : ℕ) :
    IsZero ((etaleCohomology.{u, v, uL} X R (q + 1)).obj F) :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  isZero_sectionsDerived_succ_of_injective (etaleTopology X) R (etaleSelf X) F q

end Plain

section Equivariant

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Berkovich's `Γ_{X{G}}` on étale `G`-sheaves: the smooth part of the representation of
`G` on the global sections. -/
def etaleGSheafSections :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  exactGlobalSections (etaleTopology X) R ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

instance etaleGSheafSections_additive : (etaleGSheafSections.{u, v, uL} ρ R).Additive :=
  inferInstanceAs (exactGlobalSections (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)).Additive

/-- The inclusion `Γ_{X{G}}(F) → Γ(X, b^*F)` of the smooth global sections of an étale
`G`-sheaf into the global sections of its restriction to the étale site of `X`. -/
def etaleGlobalInclusion :
    etaleGSheafSections.{u, v, uL} ρ R ⋙ smoothForget R G ⟶
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleSections.{u, v, uL} X R :=
  exactGlobalInclusion (etaleTopology X) R ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

/-- A smooth global section is sent to itself. -/
theorem etaleGlobalInclusion_app_apply (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (s : (etaleGSheafSections.{u, v, uL} ρ R ⋙ smoothForget R G).obj F) :
    ((etaleGlobalInclusion.{u, v, uL} ρ R).app F).hom s = s.1 :=
  rfl

/-- Berkovich's `Γ_{X(G)}` on étale `G`-sheaves: the `G`-invariant vectors of
`Γ_{X{G}}(F)`. -/
def etaleGSheafInvariantSections :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  exactInvariantGlobalSections (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

instance etaleGSheafInvariantSections_additive :
    (etaleGSheafInvariantSections.{u, v, uL} ρ R).Additive :=
  inferInstanceAs (exactInvariantGlobalSections (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)).Additive

variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- `Γ_{X{G}}` is left exact. -/
theorem etaleGSheafSections_preservesFiniteLimits :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    PreservesFiniteLimits (etaleGSheafSections.{u, v, uL} ρ R) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  inferInstanceAs (PreservesFiniteLimits (exactGlobalSections (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)))

/-- `Γ_{X(G)}` is left exact. -/
theorem etaleGSheafInvariantSections_preservesFiniteLimits :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    PreservesFiniteLimits (etaleGSheafInvariantSections.{u, v, uL} ρ R) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  inferInstanceAs (PreservesFiniteLimits (exactInvariantGlobalSections (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)))

/-- Berkovich's `H^q(X{G}, F)` for étale `G`-sheaves of modules, as smooth representations
of `G`: the right derived functors of `Γ_{X{G}}`, computed with injective resolutions among
étale `G`-sheaves. Sheafification and enough injectives are proved; the admissible
refinements of the distinguished lift system are a hypothesis. -/
def etaleGSheafCohomology (q : ℕ) :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  exactGlobalDerived (etaleTopology X) R ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) q

/-- In degree zero, `H^0(X{G}, F)` is `Γ_{X{G}}(F)`. -/
def etaleGSheafCohomologyZeroIso :
    etaleGSheafCohomology.{u, v, uL} ρ R 0 ≅ etaleGSheafSections.{u, v, uL} ρ R :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  exactGlobalDerivedZeroIso (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

/-- `H^q(X{G}, F)` is computed by any injective resolution among étale `G`-sheaves. -/
def etaleGSheafCohomologyIso {F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)}
    (I : haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R; InjectiveResolution F) (q : ℕ) :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    (etaleGSheafCohomology.{u, v, uL} ρ R q).obj F ≅
      (HomologicalComplex.homologyFunctor
          (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) (ComplexShape.up ℕ) q).obj
        (((etaleGSheafSections.{u, v, uL} ρ R).mapHomologicalComplex (ComplexShape.up ℕ)).obj
          I.cocomplex) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  exactGlobalDerivedIso (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) I q

/-- `H^{q+1}(X{G}, F) = 0` for étale `G`-sheaves `F` that are injective among them. -/
theorem isZero_etaleGSheafCohomology_succ_of_injective
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective F] (q : ℕ) :
    IsZero ((etaleGSheafCohomology.{u, v, uL} ρ R (q + 1)).obj F) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  isZero_exactGlobalDerived_succ_of_injective (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) F q

/-- Berkovich's `H^q(X(G), F)` for étale `G`-sheaves of modules: the right derived functors
of `Γ_{X(G)}`, computed with injective resolutions among étale `G`-sheaves. -/
def etaleGSheafInvariantCohomology (q : ℕ) :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  exactInvariantGlobalDerived (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) q

/-- In degree zero, `H^0(X(G), F)` is `Γ_{X(G)}(F)`. -/
def etaleGSheafInvariantCohomologyZeroIso :
    etaleGSheafInvariantCohomology.{u, v, uL} ρ R 0 ≅
      etaleGSheafInvariantSections.{u, v, uL} ρ R :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  exactInvariantGlobalDerivedZeroIso (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

/-- The edge map `H^q(X(G), F) → H^q(X{G}, F)^G`. -/
def etaleGlobalInvariantEdgeMap (q : ℕ) :
    etaleGSheafInvariantCohomology.{u, v, uL} ρ R q ⟶
      etaleGSheafCohomology.{u, v, uL} ρ R q ⋙
        smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  exactInvariantGlobalEdgeMap (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) q

/-- In degree zero, the edge map is an isomorphism. -/
theorem isIso_etaleGlobalInvariantEdgeMap_zero :
    IsIso (etaleGlobalInvariantEdgeMap.{u, v, uL} ρ R 0) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  isIso_exactInvariantGlobalEdgeMap_zero (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

/-- The comparison `H^q(X{G}, F) → H^q(X, b^*F)` of Berkovich's Theorem 1.6.1(ii) for étale
`G`-sheaves: the map induced in degree `q` by `etaleGlobalInclusion` through the exact
functors `b^*` and `smoothForget`. -/
def etaleComparison (q : ℕ) :
    etaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G ⟶
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCohomology.{u, v, uL} X R q :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactGlobalComparison (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) q

end Equivariant

end Langlands.Sheaf.Equivariant.Analytic
