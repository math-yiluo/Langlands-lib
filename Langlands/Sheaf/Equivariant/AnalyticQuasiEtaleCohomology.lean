import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleComparison
import Langlands.Sheaf.Equivariant.TwistedGlobalSections

/-!
# Cohomology of quasi-étale sheaves and quasi-étale `G`-sheaves

Let `G` act on an analytic space `X`. This module defines the cohomology `H^q(X, F)` of
module sheaves on the quasi-étale site of `X`, Berkovich's `H^q(X{G}, F)` of quasi-étale
`G`-sheaves as smooth representations of `G`, and the comparison maps
`H^q(X{G}, F) → H^q(X, b^*F)` of Berkovich's Theorem 1.6.1(ii). These are the constructions
of `TwistedGlobalSections` for the quasi-étale site. No family of points is involved. That
the comparison maps are isomorphisms for compact `X` is not proved.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Plain

variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Global sections `Γ(X, F)` of module sheaves on the quasi-étale site of `X`: the sections
over `X` itself. -/
def quasiEtaleSections :
    Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  sheafSectionsModule (quasiEtaleTopology X) R (quasiEtaleSelf X)

instance quasiEtaleSections_additive : (quasiEtaleSections.{u, v, uL} X R).Additive :=
  inferInstanceAs (sheafSectionsModule (quasiEtaleTopology X) R (quasiEtaleSelf X)).Additive

/-- `Γ(X, -)` is left exact. -/
instance quasiEtaleSections_preservesFiniteLimits :
    PreservesFiniteLimits (quasiEtaleSections.{u, v, uL} X R) :=
  inferInstanceAs
    (PreservesFiniteLimits (sheafSectionsModule (quasiEtaleTopology X) R (quasiEtaleSelf X)))

/-- `H^q(X, F)` for module sheaves on the quasi-étale site of `X`: the right derived functors
of `Γ(X, -)`, computed with injective resolutions of module sheaves. Sheafification and
enough injectives are proved. -/
def quasiEtaleCohomology (q : ℕ) :
    Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  sectionsDerived (quasiEtaleTopology X) R (quasiEtaleSelf X) q

/-- In degree zero, `H^0(X, F)` is `Γ(X, F)`. -/
def quasiEtaleCohomologyZeroIso :
    quasiEtaleCohomology.{u, v, uL} X R 0 ≅ quasiEtaleSections.{u, v, uL} X R :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  sectionsDerivedZeroIso (quasiEtaleTopology X) R (quasiEtaleSelf X)

/-- `H^{q+1}(X, F) = 0` for injective `F`. -/
theorem isZero_quasiEtaleCohomology_succ_of_injective
    (F : Sheaf (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) [Injective F] (q : ℕ) :
    IsZero ((quasiEtaleCohomology.{u, v, uL} X R (q + 1)).obj F) :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  isZero_sectionsDerived_succ_of_injective (quasiEtaleTopology X) R (quasiEtaleSelf X) F q

end Plain

section Equivariant

variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Berkovich's `Γ_{X{G}}` on quasi-étale `G`-sheaves: the smooth part of the representation
of `G` on the global sections. -/
def quasiEtaleGSheafSections :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  discreteGlobalSections (quasiEtaleTopology X) R (compactLiftSystem ρ)

instance quasiEtaleGSheafSections_additive :
    (quasiEtaleGSheafSections.{u, v, uL} ρ R).Additive :=
  inferInstanceAs
    (discreteGlobalSections (quasiEtaleTopology X) R (compactLiftSystem ρ)).Additive

/-- The inclusion `Γ_{X{G}}(F) → Γ(X, b^*F)` of the smooth global sections of a quasi-étale
`G`-sheaf into the global sections of its restriction to the quasi-étale site of `X`. -/
def quasiEtaleGlobalInclusion :
    quasiEtaleGSheafSections.{u, v, uL} ρ R ⋙ smoothForget R G ⟶
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ quasiEtaleSections.{u, v, uL} X R :=
  smoothGlobalInclusion (quasiEtaleTopology X) R (compactLiftSystem ρ)

theorem quasiEtaleGlobalInclusion_app_apply
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
    (s : (quasiEtaleGSheafSections.{u, v, uL} ρ R ⋙ smoothForget R G).obj F) :
    ((quasiEtaleGlobalInclusion.{u, v, uL} ρ R).app F).hom s = s.1 :=
  rfl

variable [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]

/-- `Γ_{X{G}}` is left exact. -/
theorem quasiEtaleGSheafSections_preservesFiniteLimits :
    haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
    PreservesFiniteLimits (quasiEtaleGSheafSections.{u, v, uL} ρ R) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  inferInstanceAs
    (PreservesFiniteLimits (discreteGlobalSections (quasiEtaleTopology X) R (compactLiftSystem ρ)))

/-- Berkovich's `H^q(X{G}, F)` for quasi-étale `G`-sheaves of modules, as smooth
representations of `G`: the right derived functors of `Γ_{X{G}}`, computed with injective
resolutions among quasi-étale `G`-sheaves. -/
def quasiEtaleGSheafCohomology (q : ℕ) :
    QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  discreteGlobalDerived (quasiEtaleTopology X) R (compactLiftSystem ρ) q

/-- In degree zero, `H^0(X{G}, F)` is `Γ_{X{G}}(F)`. -/
def quasiEtaleGSheafCohomologyZeroIso :
    quasiEtaleGSheafCohomology.{u, v, uL} ρ R 0 ≅ quasiEtaleGSheafSections.{u, v, uL} ρ R :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  discreteGlobalDerivedZeroIso (quasiEtaleTopology X) R (compactLiftSystem ρ)

/-- `H^{q+1}(X{G}, F) = 0` for quasi-étale `G`-sheaves `F` that are injective among them. -/
theorem isZero_quasiEtaleGSheafCohomology_succ_of_injective
    (F : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective F] (q : ℕ) :
    IsZero ((quasiEtaleGSheafCohomology.{u, v, uL} ρ R (q + 1)).obj F) :=
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  isZero_discreteGlobalDerived_succ_of_injective (quasiEtaleTopology X) R (compactLiftSystem ρ)
    F q

/-- The comparison `H^q(X{G}, F) → H^q(X, b^*F)` of Berkovich's Theorem 1.6.1(ii) for
quasi-étale `G`-sheaves: the map induced in degree `q` by `quasiEtaleGlobalInclusion` through
the exact functors `b^*` and `smoothForget`. -/
def quasiEtaleComparison (q : ℕ) :
    quasiEtaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G ⟶
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ quasiEtaleCohomology.{u, v, uL} X R q :=
  haveI := quasiEtale_hasSheafify.{u, v, uL} X R
  haveI := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  haveI := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  haveI := quasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  globalComparison (quasiEtaleTopology X) R (compactLiftSystem ρ) q

end Equivariant

end Langlands.Sheaf.Equivariant.Analytic
