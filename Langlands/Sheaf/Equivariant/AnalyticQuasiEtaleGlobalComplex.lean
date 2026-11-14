import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleCohomology
import Langlands.Sheaf.Equivariant.TwistedExactGlobalComplex

/-!
# Invariant cohomology and derived global section complexes in the quasi-étale case

Let `G` act on an analytic space `X`. This module completes the cohomology of
`AnalyticQuasiEtaleCohomology` in two ways. It defines Berkovich's invariant global
sections `Γ_{X(G)}` of quasi-étale `G`-sheaves, their derived functors `H^q(X(G), F)` and
the edge maps `H^q(X(G), F) → H^q(X{G}, F)^G`. It packages the cohomology as single
objects of bounded below derived categories: the complex `RΓ(X, F)` of a module sheaf on
the quasi-étale site of `X`, Berkovich's `RΓ(X{G}, F)` of a quasi-étale `G`-sheaf as a
complex of smooth representations of `G`, the complex `RΓ(X(G), F)`, and the comparison
`RΓ(X{G}, F) → RΓ(X, b^*F)` in the derived category of modules, whose cohomology in
degree `q` is the comparison `quasiEtaleComparison` of Berkovich's Theorem 1.6.1(ii).
These are the constructions of `TwistedExactGlobalComparison` and
`TwistedExactGlobalComplex` for the quasi-étale site, with the exact inclusion of
quasi-étale `G`-sheaves (the discrete sheaves of the compact lift system) into sheaves on
the twisted quasi-étale site. That the comparison is an isomorphism for compact `X` is
not proved.
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
sheaves on the quasi-étale site of `X`. The derived category of module sheaves used inside
is Mathlib's standard one; the resulting functor does not depend on it up to isomorphism of
cohomology. -/
def quasiEtaleComplex :
    Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  sheafSectionsComplex (quasiEtaleTopology X) R (quasiEtaleSelf X)

/-- The cohomology of `RΓ(X, F)` in degree `q` is `H^q(X, F)`. -/
def quasiEtaleComplexHomologyIso
    (F : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) q).obj
        ((quasiEtaleComplex.{u, v, uL} X R).obj F) ≅
      (quasiEtaleCohomology.{u, v, uL} X R q).obj F :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  sheafSectionsComplexHomologyIso (quasiEtaleTopology X) R (quasiEtaleSelf X) F q

/-- `RΓ(X, F)` has no cohomology in negative degrees. -/
theorem isZero_quasiEtaleComplex_homology
    (F : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) n).obj
      ((quasiEtaleComplex.{u, v, uL} X R).obj F)) :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  isZero_sheafSectionsComplex_homology (quasiEtaleTopology X) R (quasiEtaleSelf X) F hn

end Plain

section Equivariant

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Berkovich's `Γ_{X(G)}` on quasi-étale `G`-sheaves: the `G`-invariant vectors of
`Γ_{X{G}}(F)`. -/
def quasiEtaleGSheafInvariantSections :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  exactInvariantGlobalSections (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

instance quasiEtaleGSheafInvariantSections_additive :
    (quasiEtaleGSheafInvariantSections.{u, v, uL} ρ R).Additive :=
  inferInstanceAs (exactInvariantGlobalSections (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)).Additive

/-- `Γ_{X(G)}(F)` is the module of `G`-invariant vectors of `Γ_{X{G}}(F)`. -/
theorem quasiEtaleGSheafInvariantSections_eq :
    quasiEtaleGSheafInvariantSections.{u, v, uL} ρ R =
      quasiEtaleGSheafSections.{u, v, uL} ρ R ⋙
        smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  rfl

variable [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- `Γ_{X(G)}` is left exact. -/
theorem quasiEtaleGSheafInvariantSections_preservesFiniteLimits :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    PreservesFiniteLimits (quasiEtaleGSheafInvariantSections.{u, v, uL} ρ R) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  inferInstanceAs (PreservesFiniteLimits (exactInvariantGlobalSections (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)))

/-- Berkovich's `H^q(X(G), F)` for quasi-étale `G`-sheaves of modules: the right derived
functors of `Γ_{X(G)}`, computed with injective resolutions among quasi-étale
`G`-sheaves. -/
def quasiEtaleGSheafInvariantCohomology (q : ℕ) :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  exactInvariantGlobalDerived (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) q

/-- In degree zero, `H^0(X(G), F)` is `Γ_{X(G)}(F)`. -/
def quasiEtaleGSheafInvariantCohomologyZeroIso :
    quasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R 0 ≅
      quasiEtaleGSheafInvariantSections.{u, v, uL} ρ R :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  exactInvariantGlobalDerivedZeroIso (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

/-- The edge map `H^q(X(G), F) → H^q(X{G}, F)^G`. -/
def quasiEtaleGlobalInvariantEdgeMap (q : ℕ) :
    quasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R q ⟶
      quasiEtaleGSheafCohomology.{u, v, uL} ρ R q ⋙
        smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  exactInvariantGlobalEdgeMap (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) q

/-- In degree zero, the edge map is an isomorphism. -/
theorem isIso_quasiEtaleGlobalInvariantEdgeMap_zero :
    IsIso (quasiEtaleGlobalInvariantEdgeMap.{u, v, uL} ρ R 0) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  isIso_exactInvariantGlobalEdgeMap_zero (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

section Smooth

variable [HasDerivedCategory.{w₃} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]

/-- Berkovich's complex `RΓ(X{G}, F)` in the bounded below derived category of smooth
representations of `G`: `Γ_{X{G}}` derived with injective resolutions among quasi-étale
`G`-sheaves. The derived category of quasi-étale `G`-sheaves used inside is Mathlib's
standard one; the resulting functor does not depend on it up to isomorphism of
cohomology. -/
def quasiEtaleGSheafComplex :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplex (quasiEtaleTopology X) R ((compactLiftSystem ρ).discreteSheafInclusion _ _)

/-- The cohomology of `RΓ(X{G}, F)` in degree `q` is `H^q(X{G}, F)`. -/
def quasiEtaleGSheafComplexHomologyIso
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor
        (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) q).obj
        ((quasiEtaleGSheafComplex.{u, v, uL} ρ R).obj F) ≅
      (quasiEtaleGSheafCohomology.{u, v, uL} ρ R q).obj F :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplexHomologyIso (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) F q

/-- `RΓ(X{G}, F)` has no cohomology in negative degrees. -/
theorem isZero_quasiEtaleGSheafComplex_homology
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor
        (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) n).obj
        ((quasiEtaleGSheafComplex.{u, v, uL} ρ R).obj F)) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  isZero_exactGlobalComplex_homology (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) F hn

end Smooth

section Invariant

variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- Berkovich's complex `RΓ(X(G), F)` in the bounded below derived category of modules:
`Γ_{X(G)}` derived with injective resolutions among quasi-étale `G`-sheaves. -/
def quasiEtaleGSheafInvariantComplex :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactInvariantGlobalComplex (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

/-- The cohomology of `RΓ(X(G), F)` in degree `q` is `H^q(X(G), F)`. -/
def quasiEtaleGSheafInvariantComplexHomologyIso
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) q).obj
        ((quasiEtaleGSheafInvariantComplex.{u, v, uL} ρ R).obj F) ≅
      (quasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R q).obj F :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactInvariantGlobalComplexHomologyIso (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) F q

/-- `RΓ(X(G), F)` has no cohomology in negative degrees. -/
theorem isZero_quasiEtaleGSheafInvariantComplex_homology
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) n).obj
      ((quasiEtaleGSheafInvariantComplex.{u, v, uL} ρ R).obj F)) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  isZero_exactInvariantGlobalComplex_homology (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) F hn

end Invariant

section Comparison

variable [HasDerivedCategory.{w₃} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- The comparison `RΓ(X{G}, F) → RΓ(X, b^*F)` in the derived category of modules, with the
action of `G` on the source forgotten. -/
def quasiEtaleComplexComparison :
    (quasiEtaleGSheafComplex.{u, v, uL} ρ R ⋙ DerivedCategory.Plus.ι) ⋙
        (smoothForget R G).mapDerivedCategory ⟶
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙
        (quasiEtaleComplex.{u, v, uL} X R ⋙ DerivedCategory.Plus.ι) :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplexComparison (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

/-- The cohomology in degree `q` of `RΓ(X{G}, F)` with the action of `G` forgotten is the
module underlying `H^q(X{G}, F)`. -/
def quasiEtaleComplexForgetHomologyIso
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) (q : ℤ)).obj
        ((smoothForget R G).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj ((quasiEtaleGSheafComplex.{u, v, uL} ρ R).obj F))) ≅
      (smoothForget R G).obj ((quasiEtaleGSheafCohomology.{u, v, uL} ρ R q).obj F) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplexForgetHomologyIso (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) F q

/-- On cohomology in degree `q`, the comparison of complexes is the comparison
`quasiEtaleComparison : H^q(X{G}, F) → H^q(X, b^*F)` in degree `q`. -/
theorem quasiEtaleComplexComparison_homology
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) (q : ℤ)).map
        ((quasiEtaleComplexComparison.{u, v, uL} ρ R).app F) ≫
        (quasiEtaleComplexHomologyIso.{u, v, uL} X R
          ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj F) q).hom =
      (quasiEtaleComplexForgetHomologyIso.{u, v, uL} ρ R F q).hom ≫
        (quasiEtaleComparison.{u, v, uL} ρ R q).app F :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplexComparison_homology (quasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) F q

end Comparison

end Equivariant

end Langlands.Sheaf.Equivariant.Analytic
