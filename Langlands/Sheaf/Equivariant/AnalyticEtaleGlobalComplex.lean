import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology
import Langlands.Sheaf.Equivariant.TwistedExactGlobalComplex

/-!
# Derived global section complexes on the étale site and of étale `G`-sheaves

Let `G` act on an analytic space `X`. This module packages the cohomology of
`AnalyticEtaleCohomology` as single objects of bounded below derived categories: the
complex `RΓ(X, F)` of a module sheaf on the étale site of `X`, Berkovich's `RΓ(X{G}, F)`
of an étale `G`-sheaf as a complex of smooth representations of `G`, the complex
`RΓ(X(G), F)` of its invariant global sections, and the comparison
`RΓ(X{G}, F) → RΓ(X, b^*F)` in the derived category of modules, whose cohomology in degree
`q` is the comparison `H^q(X{G}, F) → H^q(X, b^*F)` of Berkovich's Theorem 1.6.1(ii). These
are the constructions of `TwistedExactGlobalComplex` for the étale site, with the inclusion
of étale `G`-sheaves into sheaves on the twisted étale site. That the comparison is an
isomorphism is not proved.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

universe u v uL z w₃ w₄

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Plain

variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- The complex `RΓ(X, F)` in the bounded below derived category of modules, for module
sheaves on the étale site of `X`. The derived category of module sheaves used inside is
Mathlib's standard one; the resulting functor does not depend on it up to isomorphism of
cohomology. -/
def etaleComplex :
    Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  sheafSectionsComplex (etaleTopology X) R (etaleSelf X)

/-- The cohomology of `RΓ(X, F)` in degree `q` is `H^q(X, F)`. -/
def etaleComplexHomologyIso
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) q).obj
        ((etaleComplex.{u, v, uL} X R).obj F) ≅
      (etaleCohomology.{u, v, uL} X R q).obj F :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  sheafSectionsComplexHomologyIso (etaleTopology X) R (etaleSelf X) F q

/-- `RΓ(X, F)` has no cohomology in negative degrees. -/
theorem isZero_etaleComplex_homology
    (F : Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) n).obj
      ((etaleComplex.{u, v, uL} X R).obj F)) :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  isZero_sheafSectionsComplex_homology (etaleTopology X) R (etaleSelf X) F hn

end Plain

section Equivariant

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

section Smooth

variable [HasDerivedCategory.{w₃} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]

/-- Berkovich's complex `RΓ(X{G}, F)` in the bounded below derived category of smooth
representations of `G`: `Γ_{X{G}}` derived with injective resolutions among étale
`G`-sheaves. The derived category of étale `G`-sheaves used inside is Mathlib's standard
one; the resulting functor does not depend on it up to isomorphism of cohomology. -/
def etaleGSheafComplex :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplex (etaleTopology X) R ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

/-- The cohomology of `RΓ(X{G}, F)` in degree `q` is `H^q(X{G}, F)`. -/
def etaleGSheafComplexHomologyIso
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor
        (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) q).obj
        ((etaleGSheafComplex.{u, v, uL} ρ R).obj F) ≅
      (etaleGSheafCohomology.{u, v, uL} ρ R q).obj F :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplexHomologyIso (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) F q

/-- `RΓ(X{G}, F)` has no cohomology in negative degrees. -/
theorem isZero_etaleGSheafComplex_homology
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
        (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) n).obj
        ((etaleGSheafComplex.{u, v, uL} ρ R).obj F)) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  isZero_exactGlobalComplex_homology (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) F hn

end Smooth

section Invariant

variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- Berkovich's complex `RΓ(X(G), F)` in the bounded below derived category of modules:
`Γ_{X(G)}` derived with injective resolutions among étale `G`-sheaves. -/
def etaleGSheafInvariantComplex :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactInvariantGlobalComplex (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

/-- The cohomology of `RΓ(X(G), F)` in degree `q` is `H^q(X(G), F)`. -/
def etaleGSheafInvariantComplexHomologyIso
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) q).obj
        ((etaleGSheafInvariantComplex.{u, v, uL} ρ R).obj F) ≅
      (etaleGSheafInvariantCohomology.{u, v, uL} ρ R q).obj F :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactInvariantGlobalComplexHomologyIso (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) F q

/-- `RΓ(X(G), F)` has no cohomology in negative degrees. -/
theorem isZero_etaleGSheafInvariantComplex_homology
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) n).obj
      ((etaleGSheafInvariantComplex.{u, v, uL} ρ R).obj F)) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  isZero_exactInvariantGlobalComplex_homology (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) F hn

end Invariant

section Comparison

variable [HasDerivedCategory.{w₃} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- The comparison `RΓ(X{G}, F) → RΓ(X, b^*F)` in the derived category of modules, with the
action of `G` on the source forgotten. -/
def etaleComplexComparison :
    (etaleGSheafComplex.{u, v, uL} ρ R ⋙ DerivedCategory.Plus.ι) ⋙
        (smoothForget R G).mapDerivedCategory ⟶
      etaleGSheafRestriction.{u, v, uL} ρ R ⋙
        (etaleComplex.{u, v, uL} X R ⋙ DerivedCategory.Plus.ι) :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplexComparison (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)

/-- The cohomology in degree `q` of `RΓ(X{G}, F)` with the action of `G` forgotten is the
module underlying `H^q(X{G}, F)`. -/
def etaleComplexForgetHomologyIso
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) (q : ℤ)).obj
        ((smoothForget R G).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj ((etaleGSheafComplex.{u, v, uL} ρ R).obj F))) ≅
      (smoothForget R G).obj ((etaleGSheafCohomology.{u, v, uL} ρ R q).obj F) :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplexForgetHomologyIso (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) F q

/-- On cohomology in degree `q`, the comparison of complexes is the comparison
`H^q(X{G}, F) → H^q(X, b^*F)` in degree `q`. -/
theorem etaleComplexComparison_homology
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) (q : ℤ)).map
        ((etaleComplexComparison.{u, v, uL} ρ R).app F) ≫
        (etaleComplexHomologyIso.{u, v, uL} X R
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj F) q).hom =
      (etaleComplexForgetHomologyIso.{u, v, uL} ρ R F q).hom ≫
        (etaleComparison.{u, v, uL} ρ R q).app F :=
  haveI := etale_hasSheafify.{u, v, uL} X R
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := etaleGSheaf_enoughInjectives.{u, v, uL} ρ R
  haveI := etale_enoughInjectives.{u, v, uL} X R
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard (Sheaf (etaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplexComparison_homology (etaleTopology X) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _) F q

end Comparison

end Equivariant

end Langlands.Sheaf.Equivariant.Analytic
