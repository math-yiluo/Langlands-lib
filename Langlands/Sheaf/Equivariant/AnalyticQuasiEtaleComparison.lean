import Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtale
import Langlands.Cohomology.DiscreteSheafDerivedComparisonHomology

/-!
# Equivariant and plain compactly supported cohomology on the quasi-étale site

Let `G` act on an analytic space `X`. This module defines the compactly supported
cohomology `H^q_c(X, F)` of module sheaves on the quasi-étale site of `X`, with supports
in the `L`-valued points, and the complex `RΓ_c(X, F)`. For quasi-étale `G`-sheaves it
defines the restriction `b^*` to the quasi-étale site of `X`, the cohomology
`H^q_c(X(G), F)` of invariant compactly supported sections with its edge map to the
invariants of `H^q_c(X{G}, F)`, and the comparison maps
`H^q_c(X{G}, F) → H^q_c(X, b^*F)` of Berkovich's Corollary 1.5.2, in each degree and as
one map of complexes. These are the published constructions of
`TwistedCompactComparison` and `DiscreteSheafDerivedComparison` for the quasi-étale
site. That the comparison maps are isomorphisms is not proved.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver Langlands.Sheaf.PointSupport
open Langlands.Cohomology Langlands.Cohomology.DiscreteSheafDerivedComparison

universe u v uL z w₃ w₄

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Size

variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Module sheaves on the quasi-étale site of `X` form a Grothendieck abelian category, so
they have enough injectives. -/
theorem quasiEtale_enoughInjectives :
    EnoughInjectives (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) :=
  haveI := quasiEtaleSite_essentiallySmall_points.{u, v, uL} X
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI : ∀ Y : (QuasiEtaleSite X)ᵒᵖ, HasLimitsOfShape
      (StructuredArrow Y (equivSmallModel.{max u (v + 1) uL} (QuasiEtaleSite X)).inverse.op)
      (ModuleCat.{max u (v + 1) uL} R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{max u (v + 1) uL} _ _
  haveI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{max u (v + 1) uL}
    (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  IsGrothendieckAbelian.enoughInjectives

/-- `X` as an object of its quasi-étale site, by its identity. -/
def quasiEtaleSelf : QuasiEtaleSite X :=
  MorphismProperty.Over.mk ⊤ (𝟙 X) ((quasiEtale (K := K)).id_mem X)

end Size

section Plain

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Compactly supported global sections `Γ_c(X, F)` of module sheaves on the quasi-étale
site of `X`, with supports in the `L`-valued points. -/
def quasiEtaleCompactSections :
    Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  letI := pointTopology L X
  sheafCompactSections (quasiEtaleTopology X) (quasiEtalePoints L h) R (quasiEtaleSelf X)

instance quasiEtaleCompactSections_additive : (quasiEtaleCompactSections L h R).Additive :=
  letI := pointTopology L X
  inferInstanceAs (sheafCompactSections (quasiEtaleTopology X) (quasiEtalePoints L h) R
    (quasiEtaleSelf X)).Additive

/-- `H^q_c(X, F)` for module sheaves on the quasi-étale site of `X`: the right derived
functors of `Γ_c(X, -)`, computed with injective resolutions of module sheaves.
Sheafification and enough injectives are proved. -/
def quasiEtaleCompactCohomology (q : ℕ) :
    Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  letI := pointTopology L X
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  compactDerived (quasiEtaleTopology X) (quasiEtalePoints L h) R (quasiEtaleSelf X) q

/-- In degree zero, `H^0_c(X, F)` is `Γ_c(X, F)`. -/
def quasiEtaleCompactCohomologyZeroIso :
    quasiEtaleCompactCohomology L h R 0 ≅ quasiEtaleCompactSections L h R :=
  letI := pointTopology L X
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  compactDerivedZeroIso (quasiEtaleTopology X) (quasiEtalePoints L h) R (quasiEtaleSelf X)

variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- The complex `RΓ_c(X, F)` in the bounded below derived category of modules. The derived
category of module sheaves used inside is Mathlib's standard one; the resulting functor
does not depend on it. -/
def quasiEtaleCompactComplex :
    Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (ModuleCat.{max u (v + 1) uL} R) :=
  letI := pointTopology L X
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  DiscreteSheafDerivedComplex.sheafCompactComplex (quasiEtaleTopology X) (quasiEtalePoints L h)
    R (quasiEtaleSelf X)

/-- The cohomology of `RΓ_c(X, F)` in degree `q` is `H^q_c(X, F)`. -/
def quasiEtaleCompactComplexHomologyIso
    (F : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) q).obj
        ((quasiEtaleCompactComplex L h R).obj F) ≅
      (quasiEtaleCompactCohomology L h R q).obj F :=
  letI := pointTopology L X
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  DiscreteSheafDerivedComplex.sheafCompactComplexHomologyIso (quasiEtaleTopology X)
    (quasiEtalePoints L h) R (quasiEtaleSelf X) F q

/-- `RΓ_c(X, F)` has no cohomology in negative degrees. -/
theorem isZero_quasiEtaleCompactComplex_homology
    (F : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) n).obj
      ((quasiEtaleCompactComplex L h R).obj F)) :=
  letI := pointTopology L X
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  DiscreteSheafDerivedComplex.isZero_sheafCompactComplex_homology (quasiEtaleTopology X)
    (quasiEtalePoints L h) R (quasiEtaleSelf X) F hn

end Plain

section Restriction

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R] [TopologicalSpace G]

/-- Berkovich's `b^*` on quasi-étale `G`-sheaves: the inclusion into sheaves on the twisted
quasi-étale site followed by restriction to the quasi-étale site of `X`, which forgets the
action of `G`. -/
def quasiEtaleGSheafRestriction :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  discreteRestriction (quasiEtaleTopology X) R (compactLiftSystem ρ)

/-- `b^*` is additive. -/
theorem quasiEtaleGSheafRestriction_additive :
    (quasiEtaleGSheafRestriction.{u, v, uL} ρ R).Additive where
  map_add := rfl

variable [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- `b^*` preserves finite limits. -/
theorem quasiEtaleGSheafRestriction_preservesFiniteLimits :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    PreservesFiniteLimits (quasiEtaleGSheafRestriction.{u, v, uL} ρ R) :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  discreteRestriction_preservesFiniteLimits (quasiEtaleTopology X) (compactLiftSystem ρ)

/-- `b^*` preserves finite colimits. -/
theorem quasiEtaleGSheafRestriction_preservesFiniteColimits :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    PreservesFiniteColimits (quasiEtaleGSheafRestriction.{u, v, uL} ρ R) :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  discreteRestriction_preservesFiniteColimits (quasiEtaleTopology X) (compactLiftSystem ρ)

end Restriction

section Comparison

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, QuasiEtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- The inclusion `Γ_{c,X{G}}(F) → Γ_c(X, b^*F)` of the smooth compactly supported global
sections of a quasi-étale `G`-sheaf into the compactly supported global sections of its
restriction to the quasi-étale site of `X`. -/
def quasiEtaleCompactInclusion :
    quasiEtaleGSheafCompactSections L ρ h R ⋙ smoothForget R G ⟶
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ quasiEtaleCompactSections L h R :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  smoothCompactInclusion (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h)

/-- Berkovich's `Γ_{c,X(G)}` on quasi-étale `G`-sheaves: the `G`-invariant vectors of
`Γ_{c,X{G}}(F)`. -/
def quasiEtaleGSheafInvariantCompactSections :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  discreteInvariantCompactSections (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h)

/-- `Γ_{c,X(G)}` is `Γ_{c,X{G}}` followed by the `G`-invariants. -/
theorem quasiEtaleGSheafInvariantCompactSections_eq :
    quasiEtaleGSheafInvariantCompactSections L ρ h R =
      quasiEtaleGSheafCompactSections L ρ h R ⋙
        smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  rfl

variable [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- Berkovich's `H^q_c(X(G), F)` for quasi-étale `G`-sheaves of modules: the right derived
functors of `Γ_{c,X(G)}`, computed with injective resolutions among quasi-étale
`G`-sheaves. -/
def quasiEtaleGSheafInvariantCompactCohomology (q : ℕ) :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  discreteInvariantCompactDerived (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h) q

/-- In degree zero, `H^0_c(X(G), F)` is `Γ_{c,X(G)}(F)`. -/
def quasiEtaleGSheafInvariantCompactCohomologyZeroIso :
    quasiEtaleGSheafInvariantCompactCohomology L ρ h R 0 ≅
      quasiEtaleGSheafInvariantCompactSections L ρ h R :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  discreteInvariantCompactDerivedZeroIso (quasiEtaleTopology X) (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h)

/-- The edge map `H^q_c(X(G), F) → H^q_c(X{G}, F)^G`. -/
def quasiEtaleInvariantEdgeMap (q : ℕ) :
    quasiEtaleGSheafInvariantCompactCohomology L ρ h R q ⟶
      quasiEtaleGSheafCompactCohomology L ρ h R q ⋙
        smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  invariantEdgeMap (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h) q

/-- In degree zero, the edge map is an isomorphism. -/
theorem isIso_quasiEtaleInvariantEdgeMap_zero :
    IsIso (quasiEtaleInvariantEdgeMap L ρ h R 0) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  isIso_invariantEdgeMap_zero (quasiEtaleTopology X) (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h)

/-- The comparison `H^q_c(X{G}, F) → H^q_c(X, b^*F)` of Berkovich's Corollary 1.5.2(i)
for quasi-étale `G`-sheaves: the map induced in degree `q` by `quasiEtaleCompactInclusion`
through the exact functors `b^*` and `smoothForget`. -/
def quasiEtaleCompactComparison (q : ℕ) :
    quasiEtaleGSheafCompactCohomology L ρ h R q ⋙ smoothForget R G ⟶
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ quasiEtaleCompactCohomology L h R q :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  compactComparison (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h) q

variable [HasDerivedCategory.{w₃} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]
variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- The comparison `RΓ_c(X{G}, F) → RΓ_c(X, b^*F)` in the derived category of modules, with
the action of `G` on the source forgotten. -/
def quasiEtaleCompactComplexComparison :
    (quasiEtaleGSheafCompactComplex L ρ h R ⋙ DerivedCategory.Plus.ι) ⋙
        (smoothForget R G).mapDerivedCategory ⟶
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙
        (quasiEtaleCompactComplex L h R ⋙ DerivedCategory.Plus.ι) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  compactComplexComparison (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h)

/-- The cohomology in degree `q` of `RΓ_c(X{G}, F)` with the action of `G` forgotten is the
module underlying `H^q_c(X{G}, F)`. -/
def quasiEtaleCompactComplexForgetHomologyIso
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) (q : ℤ)).obj
        ((smoothForget R G).mapDerivedCategory.obj
          (DerivedCategory.Plus.ι.obj ((quasiEtaleGSheafCompactComplex L ρ h R).obj F))) ≅
      (smoothForget R G).obj ((quasiEtaleGSheafCompactCohomology L ρ h R q).obj F) :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  compactComplexForgetHomologyIso (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h) F q

/-- On cohomology in degree `q`, the comparison of complexes is the comparison
`H^q_c(X{G}, F) → H^q_c(X, b^*F)` in degree `q`. -/
theorem quasiEtaleCompactComplexComparison_homology
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) (q : ℤ)).map
        ((quasiEtaleCompactComplexComparison L ρ h R).app F) ≫
        (quasiEtaleCompactComplexHomologyIso L h R
          ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj F) q).hom =
      (quasiEtaleCompactComplexForgetHomologyIso L ρ h R F q).hom ≫
        (quasiEtaleCompactComparison L ρ h R q).app F :=
  letI := pointTopology L X
  letI := EtaleSite.pointAction L ρ
  haveI := continuousConstSMul_pointAction L ρ
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  letI := HasDerivedCategory.standard (QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  letI := HasDerivedCategory.standard
    (Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  compactComplexComparison_homology (quasiEtaleTopology X) R (compactLiftSystem ρ)
    (QuasiEtaleSite.pointEquivariance L ρ h) F q

end Comparison

end Langlands.Sheaf.Equivariant.Analytic
