import Langlands.Sheaf.Equivariant.TwistedExactCompactComparison
import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactCohomology

/-!
# Equivariant and plain compactly supported cohomology on the étale site

Let `G` act on an analytic space `X`. This module defines the compactly supported
cohomology `H^q_c(X, F)` of module sheaves on the étale site of `X`, with supports in the
`L`-valued points, and the complex `RΓ_c(X, F)`. For Berkovich's étale `G`-sheaves it
defines the restriction `b^*` to the étale site of `X`, the cohomology `H^q_c(X(G), F)`
of invariant compactly supported sections with its edge map to the invariants of
`H^q_c(X{G}, F)`, and the comparison maps `H^q_c(X{G}, F) → H^q_c(X, b^*F)` of
Berkovich's Corollary 1.5.2, in each degree and as one map of complexes. These are the
constructions of `TwistedExactCompactComparison` for the étale site, with the inclusion
of étale `G`-sheaves into sheaves on the twisted étale site. That the comparison maps are
isomorphisms is not proved.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport
open Langlands.Cohomology

universe u v uL z w₃ w₄

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Size

variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Module sheaves on the étale site of `X` form a Grothendieck abelian category, so they
have enough injectives. -/
theorem etale_enoughInjectives :
    EnoughInjectives (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) :=
  haveI := etaleSite_essentiallySmall_points.{u, v, uL} X
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI : ∀ Y : (EtaleSite X)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Y (equivSmallModel.{max u (v + 1) uL} (EtaleSite X)).inverse.op)
      (ModuleCat.{max u (v + 1) uL} R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL} _ _
  haveI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u (v + 1) uL}
    (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)
  haveI := etale_hasSheafify.{u, v, uL} X R
  IsGrothendieckAbelian.enoughInjectives

/-- `X` as an object of its étale site, by its identity. -/
def etaleSelf : EtaleSite X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) ((etale (K := K)).id_mem X)

end Size

section Induction

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- If `G` is small at the universe `max u (v + 1) uL`, every module presheaf on the étale
site has a pointwise right Kan extension along the inclusion into the twisted étale site:
the indexing categories are essentially small. -/
theorem etale_hasPointwiseRightKanExtension [Small.{max u (v + 1) uL} G]
    (F : (EtaleSite X)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R) :
    (ι (etale (K := K)) ρ).op.HasPointwiseRightKanExtension F := fun Y =>
  haveI := etaleSite_essentiallySmall_points.{u, v, uL} X
  haveI := twistedEtale_locallySmall_points.{u, v, uL} X ρ
  haveI := hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL}
    (StructuredArrow Y (ι (etale (K := K)) ρ).op) (ModuleCat.{max u (v + 1) uL} R)
  inferInstance

end Induction

section Plain

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Compactly supported global sections `Γ_c(X, F)` of module sheaves on the étale site
of `X`, with supports in the `L`-valued points. -/
def etaleCompactSections :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  letI := pointTopology L X
  sheafCompactSections (etaleTopology X) (etalePoints L h) R (etaleSelf X)

instance etaleCompactSections_additive : (etaleCompactSections L h R).Additive :=
  letI := pointTopology L X
  inferInstanceAs (sheafCompactSections (etaleTopology X) (etalePoints L h) R
    (etaleSelf X)).Additive

/-- `H^q_c(X, F)` for module sheaves on the étale site of `X`: the right derived functors
of `Γ_c(X, -)`, computed with injective resolutions of module sheaves. Sheafification and
enough injectives are proved. -/
def etaleCompactCohomology (q : ℕ) :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  letI := pointTopology L X
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  compactDerived (etaleTopology X) (etalePoints L h) R (etaleSelf X) q

/-- In degree zero, `H^0_c(X, F)` is `Γ_c(X, F)`. -/
def etaleCompactCohomologyZeroIso :
    etaleCompactCohomology L h R 0 ≅ etaleCompactSections L h R :=
  letI := pointTopology L X
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  compactDerivedZeroIso (etaleTopology X) (etalePoints L h) R (etaleSelf X)

variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- The complex `RΓ_c(X, F)` in the bounded below derived category of modules. The derived
category of module sheaves used inside is Mathlib's standard one; the resulting functor
does not depend on it. -/
def etaleCompactComplex :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (ModuleCat.{max u (v + 1) uL} R) :=
  letI := pointTopology L X
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  DiscreteSheafDerivedComplex.sheafCompactComplex (etaleTopology X) (etalePoints L h) R
    (etaleSelf X)

/-- The cohomology of `RΓ_c(X, F)` in degree `q` is `H^q_c(X, F)`. -/
def etaleCompactComplexHomologyIso
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) q).obj
        ((etaleCompactComplex L h R).obj F) ≅
      (etaleCompactCohomology L h R q).obj F :=
  letI := pointTopology L X
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  DiscreteSheafDerivedComplex.sheafCompactComplexHomologyIso (etaleTopology X)
    (etalePoints L h) R (etaleSelf X) F q

/-- `RΓ_c(X, F)` has no cohomology in negative degrees. -/
theorem isZero_etaleCompactComplex_homology
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) n).obj
      ((etaleCompactComplex L h R).obj F)) :=
  letI := pointTopology L X
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  DiscreteSheafDerivedComplex.isZero_sheafCompactComplex_homology (etaleTopology X)
    (etalePoints L h) R (etaleSelf X) F hn

end Plain

section Restriction

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R] [TopologicalSpace G]

/-- Berkovich's `b^*` on étale `G`-sheaves: the inclusion into sheaves on the twisted étale
site followed by restriction to the étale site of `X`, which forgets the action of `G`. -/
def etaleGSheafRestriction :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  exactRestriction (etaleTopology X) R ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

/-- `b^*` is additive. -/
instance etaleGSheafRestriction_additive : (etaleGSheafRestriction.{u, v, uL} ρ R).Additive :=
  inferInstanceAs (exactRestriction (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)).Additive

variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- `b^*` preserves finite limits. -/
theorem etaleGSheafRestriction_preservesFiniteLimits :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    PreservesFiniteLimits (etaleGSheafRestriction.{u, v, uL} ρ R) :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  exactRestriction_preservesFiniteLimits (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

/-- `b^*` preserves finite colimits. -/
theorem etaleGSheafRestriction_preservesFiniteColimits :
    haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
    PreservesFiniteColimits (etaleGSheafRestriction.{u, v, uL} ρ R) :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactRestriction_preservesFiniteColimits (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

end Restriction

section Comparison

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The inclusion `Γ_{c,X{G}}(F) → Γ_c(X, b^*F)` of the smooth compactly supported global
sections of an étale `G`-sheaf into the compactly supported global sections of its
restriction to the étale site of `X`. -/
def etaleCompactInclusion :
    etaleGSheafCompactSections L ρ h R ⋙ smoothForget R G ⟶
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCompactSections L h R :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  exactCompactInclusion (etaleTopology X) R ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)
    (EtaleSite.pointEquivariance L ρ h)

/-- Berkovich's `Γ_{c,X(G)}` on étale `G`-sheaves: the `G`-invariant vectors of
`Γ_{c,X{G}}(F)`. -/
def etaleGSheafInvariantCompactSections :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  etaleGSheafCompactSections L ρ h R ⋙
    smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G

instance etaleGSheafInvariantCompactSections_additive :
    (etaleGSheafInvariantCompactSections L ρ h R).Additive :=
  inferInstanceAs (etaleGSheafCompactSections L ρ h R ⋙
    smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G).Additive

variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- Berkovich's `H^q_c(X(G), F)` for étale `G`-sheaves of modules: the right derived
functors of `Γ_{c,X(G)}`, computed with injective resolutions among étale `G`-sheaves. -/
def etaleGSheafInvariantCompactCohomology (q : ℕ) :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  (etaleGSheafInvariantCompactSections L ρ h R).rightDerived q

/-- In degree zero, `H^0_c(X(G), F)` is `Γ_{c,X(G)}(F)`. -/
def etaleGSheafInvariantCompactCohomologyZeroIso :
    etaleGSheafInvariantCompactCohomology L ρ h R 0 ≅
      etaleGSheafInvariantCompactSections L ρ h R :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  exactInvariantCompactDerivedZeroIso (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) (EtaleSite.pointEquivariance L ρ h)

/-- The edge map `H^q_c(X(G), F) → H^q_c(X{G}, F)^G`. -/
def etaleInvariantEdgeMap (q : ℕ) :
    etaleGSheafInvariantCompactCohomology L ρ h R q ⟶
      etaleGSheafCompactCohomology L ρ h R q ⋙
        smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  exactInvariantEdgeMap (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) (EtaleSite.pointEquivariance L ρ h) q

/-- In degree zero, the edge map is an isomorphism. -/
theorem isIso_etaleInvariantEdgeMap_zero :
    IsIso (etaleInvariantEdgeMap L ρ h R 0) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  isIso_exactInvariantEdgeMap_zero (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) (EtaleSite.pointEquivariance L ρ h)

/-- The comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` of Berkovich's Corollary 1.5.2(i) for
étale `G`-sheaves: the map induced in degree `q` by `etaleCompactInclusion` through the
exact functors `b^*` and `smoothForget`. -/
def etaleCompactComparison (q : ℕ) :
    etaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G ⟶
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCompactCohomology L h R q :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactCompactComparison (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) (EtaleSite.pointEquivariance L ρ h) q

variable [HasDerivedCategory.{w₃} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- The comparison `RΓ_c(X{G}, F) → RΓ_c(X, b^*F)` in the derived category of modules,
with the action of `G` on the source forgotten. -/
def etaleCompactComplexComparison :
    (etaleGSheafCompactComplex L ρ h R ⋙ DerivedCategory.Plus.ι) ⋙
        (smoothForget R G).mapDerivedCategory ⟶
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙
        (etaleCompactComplex L h R ⋙ DerivedCategory.Plus.ι) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  exactCompactComplexComparison (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) (EtaleSite.pointEquivariance L ρ h)

/-- The cohomology in degree `q` of `RΓ_c(X{G}, F)` with the action of `G` forgotten is the
module underlying `H^q_c(X{G}, F)`. -/
def etaleCompactComplexForgetHomologyIso
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) (q : ℤ)).obj
        ((smoothForget R G).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj ((etaleGSheafCompactComplex L ρ h R).obj F))) ≅
      (smoothForget R G).obj ((etaleGSheafCompactCohomology L ρ h R q).obj F) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  exactCompactComplexForgetHomologyIso (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) (EtaleSite.pointEquivariance L ρ h) F q

/-- On cohomology in degree `q`, the comparison of complexes is the comparison
`H^q_c(X{G}, F) → H^q_c(X, b^*F)` in degree `q`. -/
theorem etaleCompactComplexComparison_homology
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) (q : ℤ)).map
        ((etaleCompactComplexComparison L ρ h R).app F) ≫
        (etaleCompactComplexHomologyIso L h R
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj F) q).hom =
      (etaleCompactComplexForgetHomologyIso L ρ h R F q).hom ≫
        (etaleCompactComparison L ρ h R q).app F :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := etaleSite_locallySmall_points.{u, v, uL} X
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  exactCompactComplexComparison_homology (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) (EtaleSite.pointEquivariance L ρ h) F q

end Comparison

end Langlands.Sheaf.Equivariant.Analytic
