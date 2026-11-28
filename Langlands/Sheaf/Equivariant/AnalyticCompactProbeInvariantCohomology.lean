import Langlands.Sheaf.Equivariant.AnalyticCompactProbeGlobalCohomology
import Langlands.Sheaf.Equivariant.TwistedConstantAdjunction
import Langlands.Sheaf.Equivariant.TwistedRepCohomology

/-! # Invariant cohomology and constant coefficients on the compact-probe site -/

noncomputable section

universe u v uL z w₄

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G] (ρ : G →* Aut X)
  (R : Type (max u (v + 1) uL)) [CommRing R] [TopologicalSpace G]

section InvariantCohomology

variable [IsTopologicalGroup G]

/-- Berkovich's `Γ_{X(G)}` on quasi-étale `G`-sheaves: the `G`-invariant vectors of
`Γ_{X{G}}(F)`. -/
def compactProbeQuasiEtaleGSheafInvariantSections :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  exactInvariantGlobalSections (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

instance compactProbeQuasiEtaleGSheafInvariantSections_additive :
    (compactProbeQuasiEtaleGSheafInvariantSections.{u, v, uL} ρ R).Additive :=
  inferInstanceAs (exactInvariantGlobalSections (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)).Additive

/-- `Γ_{X(G)}(F)` is the module of `G`-invariant vectors of `Γ_{X{G}}(F)`. -/
theorem compactProbeQuasiEtaleGSheafInvariantSections_eq :
    compactProbeQuasiEtaleGSheafInvariantSections.{u, v, uL} ρ R =
      compactProbeQuasiEtaleGSheafSections.{u, v, uL} ρ R ⋙
        smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  rfl

variable [Small.{max u (v + 1) uL} G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedCompactProbeQuasiEtaleTopology ρ)]

/-- `Γ_{X(G)}` is left exact. -/
theorem compactProbeQuasiEtaleGSheafInvariantSections_preservesFiniteLimits :
    haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
    PreservesFiniteLimits (compactProbeQuasiEtaleGSheafInvariantSections.{u, v, uL} ρ R) :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  inferInstanceAs (PreservesFiniteLimits (exactInvariantGlobalSections (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)))

/-- Berkovich's `H^q(X(G), F)` for quasi-étale `G`-sheaves of modules: the right derived
functors of `Γ_{X(G)}`, computed with injective resolutions among quasi-étale
`G`-sheaves. -/
def compactProbeQuasiEtaleGSheafInvariantCohomology (q : ℕ) :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤ ModuleCat.{max u (v + 1) uL} R :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  exactInvariantGlobalDerived (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) q

/-- In degree zero, `H^0(X(G), F)` is `Γ_{X(G)}(F)`. -/
def compactProbeQuasiEtaleGSheafInvariantCohomologyZeroIso :
    compactProbeQuasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R 0 ≅
      compactProbeQuasiEtaleGSheafInvariantSections.{u, v, uL} ρ R :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  exactInvariantGlobalDerivedZeroIso (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

/-- The edge map `H^q(X(G), F) → H^q(X{G}, F)^G`. -/
def compactProbeQuasiEtaleGlobalInvariantEdgeMap (q : ℕ) :
    compactProbeQuasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R q ⟶
      compactProbeQuasiEtaleGSheafCohomology.{u, v, uL} ρ R q ⋙
        smoothInvariantsFunctor.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  exactInvariantGlobalEdgeMap (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) q

/-- In degree zero, the edge map is an isomorphism. -/
theorem isIso_compactProbeQuasiEtaleGlobalInvariantEdgeMap_zero :
    IsIso (compactProbeQuasiEtaleGlobalInvariantEdgeMap.{u, v, uL} ρ R 0) :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  isIso_exactInvariantGlobalEdgeMap_zero (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

section Invariant

variable [HasDerivedCategory.{w₄} (ModuleCat.{max u (v + 1) uL} R)]

/-- Berkovich's complex `RΓ(X(G), F)` in the bounded below derived category of modules:
`Γ_{X(G)}` derived with injective resolutions among quasi-étale `G`-sheaves. -/
def compactProbeQuasiEtaleGSheafInvariantComplex :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactInvariantGlobalComplex (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

/-- The cohomology of `RΓ(X(G), F)` in degree `q` is `H^q(X(G), F)`. -/
def compactProbeQuasiEtaleGSheafInvariantComplexHomologyIso
    (F : CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) q).obj
        ((compactProbeQuasiEtaleGSheafInvariantComplex.{u, v, uL} ρ R).obj F) ≅
      (compactProbeQuasiEtaleGSheafInvariantCohomology.{u, v, uL} ρ R q).obj F :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactInvariantGlobalComplexHomologyIso (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) F q

/-- `RΓ(X(G), F)` has no cohomology in negative degrees. -/
theorem isZero_compactProbeQuasiEtaleGSheafInvariantComplex_homology
    (F : CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) {n : ℤ} (hn : n < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) n).obj
      ((compactProbeQuasiEtaleGSheafInvariantComplex.{u, v, uL} ρ R).obj F)) :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard (CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  isZero_exactInvariantGlobalComplex_homology (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) F hn

end Invariant

end InvariantCohomology

variable [Small.{max u (v + 1) uL} G]

section Restriction

/-- `H^q(X, b^*F)` for quasi-étale `G`-sheaves of modules, as representations of `G`: the
right derived functors of the global sections representation on the twisted quasi-étale site,
applied to the inclusion of quasi-étale `G`-sheaves. -/
def compactProbeQuasiEtaleRestrictionCohomologyRep (q : ℕ) :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      Rep.{max u (v + 1) uL} R G :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  (compactLiftSystem ρ).discreteSheafInclusion _ _ ⋙
    sheafGlobalRepDerived (compactProbeQuasiEtaleTopology X) R q

/-- The module underlying `compactProbeQuasiEtaleRestrictionCohomologyRep ρ R q` is `H^q(X, b^*F)`. -/
def compactProbeQuasiEtaleRestrictionCohomologyForgetIso (q : ℕ) :
    compactProbeQuasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q ⋙
        forget₂ (Rep.{max u (v + 1) uL} R G) (ModuleCat.{max u (v + 1) uL} R) ≅
      compactProbeQuasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ compactProbeQuasiEtaleCohomology.{u, v, uL} X R q :=
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  haveI := DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uL} (G := G) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uL} (G := G) R
  Functor.isoWhiskerLeft ((compactLiftSystem ρ).discreteSheafInclusion _ _)
    (restrictionGlobalCohomologyIso (compactProbeQuasiEtaleTopology X) R q)

/-- The canonical action of `G` on `H^q(X, b^*F)` for a quasi-étale `G`-sheaf `F`: the action
on `compactProbeQuasiEtaleRestrictionCohomologyRep ρ R q`, transported along
`compactProbeQuasiEtaleRestrictionCohomologyForgetIso`. -/
def compactProbeQuasiEtaleRestrictionCohomologyAction (q : ℕ)
    (F : CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Representation R G ((compactProbeQuasiEtaleCohomology.{u, v, uL} X R q).obj
      ((compactProbeQuasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj F)) :=
  (LinearEquiv.conjAlgEquiv R
    ((compactProbeQuasiEtaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app
      F).toLinearEquiv).toMonoidHom.comp
    ((compactProbeQuasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F).ρ

/-- The isomorphism `compactProbeQuasiEtaleRestrictionCohomologyForgetIso` intertwines the two actions. -/
theorem compactProbeQuasiEtaleRestrictionCohomologyAction_apply (q : ℕ)
    (F : CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (g : G)
    (x : (compactProbeQuasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F) :
    compactProbeQuasiEtaleRestrictionCohomologyAction.{u, v, uL} ρ R q F g
        (((compactProbeQuasiEtaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).hom x) =
      ((compactProbeQuasiEtaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).hom
        (((compactProbeQuasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F).ρ g x) := by
  let e := ((compactProbeQuasiEtaleRestrictionCohomologyForgetIso.{u, v, uL} ρ R q).app F).toLinearEquiv
  change e ((((compactProbeQuasiEtaleRestrictionCohomologyRep.{u, v, uL} ρ R q).obj F).ρ g)
    (e.symm (e x))) = e _
  rw [LinearEquiv.symm_apply_apply]

end Restriction

variable [IsTopologicalGroup G]

section Constant

variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedCompactProbeQuasiEtaleTopology ρ)]

/-- The constant quasi-étale `G`-sheaf of a smooth representation of `G`: the sheafification
of the presheaf that is `M` on every object of the twisted quasi-étale site, where a twisted
morphism with twist `g` acts by `g⁻¹`. -/
def compactProbeQuasiEtaleConstantGSheaf :
    SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G ⥤
      CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  discreteConstantTwisted (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)
    (isLiftSystem_liftSystem _)

/-- The constant quasi-étale `G`-sheaf functor is left adjoint to `Γ_{X{G}}`. -/
def compactProbeQuasiEtaleConstantGSheafAdjunction :
    compactProbeQuasiEtaleConstantGSheaf.{u, v, uL} ρ R ⊣ compactProbeQuasiEtaleGSheafSections.{u, v, uL} ρ R :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  discreteConstantTwistedAdjunction (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)
    (isLiftSystem_liftSystem _)

omit [IsTopologicalGroup G] in
/-- The constant quasi-étale `G`-sheaf functor preserves monomorphisms. -/
theorem compactProbeQuasiEtaleConstantGSheaf_preservesMonomorphisms :
    (compactProbeQuasiEtaleConstantGSheaf.{u, v, uL} ρ R).PreservesMonomorphisms :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  discreteConstantTwisted_preservesMonomorphisms (compactProbeQuasiEtaleTopology X) R
    (compactLiftSystem ρ) (isLiftSystem_liftSystem _)

/-- `Γ_{X{G}}` sends injective quasi-étale `G`-sheaves to injective smooth representations of
`G`. -/
theorem compactProbeQuasiEtaleGSheafSections_preservesInjectiveObjects :
    (compactProbeQuasiEtaleGSheafSections.{u, v, uL} ρ R).PreservesInjectiveObjects :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  discreteGlobalSections_preservesInjectiveObjects (compactProbeQuasiEtaleTopology X) R
    (compactLiftSystem ρ) (isLiftSystem_liftSystem _)

end Constant

end Langlands.Sheaf.Equivariant.Analytic
