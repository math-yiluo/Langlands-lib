import Langlands.Sheaf.Equivariant.AnalyticCompactProbeGlobalCohomology
import Langlands.Sheaf.Equivariant.TwistedRepCohomology
import Langlands.Cohomology.AnalyticGlobalSpectralSequence.Statement
import Mathlib.Topology.Compactness.Paracompact

/-!
# Ordinary and smooth cohomology comparisons on the compact-probe site

Berkovich, *Étale equivariant sheaves on p-adic analytic spaces*, Theorem
1.6.1(i)–(ii), in the module-valued quasi-étale case.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic Langlands.Sheaf.Equivariant.TwistedOver

set_option autoImplicit false
set_option quotPrecheck false

universe u v uR z wRep wMod

namespace Langlands.Cohomology.AnalyticCompactProbeGlobalComparison

open AnalyticGlobalComposite AnalyticGlobalSpectralSequence

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Small.{max u (v + 1) uR} G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uR)) [CommRing R]

section Maps

variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedCompactProbeQuasiEtaleTopology ρ)]

/-- The comparison between deriving ordinary sections after restriction
and applying ordinary cohomology to the restriction. -/
def restrictedSectionsComparison (q : ℕ) :
    haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uR} ρ R
    haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uR} ρ R
    (compactProbeQuasiEtaleGSheafRestriction.{u, v, uR} ρ R ⋙
      compactProbeQuasiEtaleSections.{u, v, uR} X R).rightDerived q ⟶
      compactProbeQuasiEtaleGSheafRestriction.{u, v, uR} ρ R ⋙
        compactProbeQuasiEtaleCohomology.{u, v, uR} X R q :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uR} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uR} ρ R
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uR} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uR} X R
  haveI := DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uR} ρ R
  let J := compactProbeQuasiEtaleTopology X
  haveI := discreteRestriction_preservesFiniteLimits (R := R) J (compactLiftSystem ρ)
  haveI := discreteRestriction_preservesFiniteColimits (R := R) J (compactLiftSystem ρ)
  ExactBaseChange.compComparisonNatTrans (compactProbeQuasiEtaleGSheafRestriction.{u, v, uR} ρ R)
    (compactProbeQuasiEtaleSections.{u, v, uR} X R) q

variable [HasDerivedCategory.{wRep} (SmoothRep.{max u (v + 1) uR, z, max u (v + 1) uR} R G)]
variable [HasDerivedCategory.{wMod} (ModuleCat.{max u (v + 1) uR} R)]

/-- The actual comparison of derived global sections on the compact-probe
site, with the action on the source forgotten exactly. -/
def globalDerivedComparison :
    (compactProbeQuasiEtaleGSheafGlobalComplex.{u, v, uR} ρ R ⋙ DerivedCategory.Plus.ι) ⋙
        (smoothForget R G).mapDerivedCategory ⟶
      compactProbeQuasiEtaleGSheafRestriction.{u, v, uR} ρ R ⋙
        (compactProbeQuasiEtaleGlobalComplex.{u, v, uR} X R ⋙ DerivedCategory.Plus.ι) :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uR} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uR} ρ R
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uR} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uR} X R
  haveI := DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uR} ρ R
  letI := HasDerivedCategory.standard
    (CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uR} R))
  letI := HasDerivedCategory.standard
    (Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uR} R))
  exactGlobalComplexComparison (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

end Maps

/-- Derived ordinary global sections on the twisted site, retaining the `G`-action. -/
def restrictedCohomologyRep (q : ℕ) :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uR} R) ⥤
      Rep.{max u (v + 1) uR} R G :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uR} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uR} ρ R
  (compactLiftSystem ρ).discreteSheafInclusion _ _ ⋙
    sheafGlobalRepDerived (compactProbeQuasiEtaleTopology X) R q

/-- The underlying modules are the ordinary cohomology of the restricted sheaves. -/
def restrictedCohomologyForgetIso (q : ℕ) :
    restrictedCohomologyRep.{u, v, uR} ρ R q ⋙
        forget₂ (Rep.{max u (v + 1) uR} R G) (ModuleCat.{max u (v + 1) uR} R) ≅
      compactProbeQuasiEtaleGSheafRestriction.{u, v, uR} ρ R ⋙
        compactProbeQuasiEtaleCohomology.{u, v, uR} X R q :=
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uR} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uR} X R
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uR} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uR} ρ R
  haveI := DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uR} ρ R
  haveI := discrete_hasColimitsOfShape.{max u (v + 1) uR} (G := G) R
  haveI := discrete_hasExactColimitsOfShape.{max u (v + 1) uR} (G := G) R
  Functor.isoWhiskerLeft ((compactLiftSystem ρ).discreteSheafInclusion _ _)
    (restrictionGlobalCohomologyIso (compactProbeQuasiEtaleTopology X) R q)

/-- The induced action on the ordinary cohomology of a restricted sheaf. -/
def restrictedCohomologyAction (q : ℕ)
    (F : CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uR} R)) :
    Representation R G ((compactProbeQuasiEtaleCohomology.{u, v, uR} X R q).obj
      ((compactProbeQuasiEtaleGSheafRestriction.{u, v, uR} ρ R).obj F)) :=
  (LinearEquiv.conjAlgEquiv R
    ((restrictedCohomologyForgetIso.{u, v, uR} ρ R q).app F).toLinearEquiv).toMonoidHom.comp
    ((restrictedCohomologyRep.{u, v, uR} ρ R q).obj F).ρ

/-- The right derived functors of invariant global sections. -/
def invariantCohomology
    [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedCompactProbeQuasiEtaleTopology ρ)]
    (q : ℕ) :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uR} R) ⥤
      ModuleCat.{max u (v + 1) uR} R :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uR} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uR} ρ R
  exactInvariantGlobalDerived (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) q

/-- The smooth group cohomology spectral sequence in Theorem 1.6.1(ii), for the
compact-probe topology. The underlying action in the second page is smooth. -/
def CompactProbeQuasiEtaleSpectralSequenceStatement : Prop :=
  ∀ (hX : T2Space (localizedSpaceFunctor.obj X)) (hρ : IsContinuousAction ρ),
    letI := compactProbe_hasFiniteEquivariantRefinements ρ hX hρ
    CompactSpace (localizedSpaceFunctor.obj X) →
    ∀ [HasDerivedCategory.{wRep} (SmoothRep.{max u (v + 1) uR, z, max u (v + 1) uR} R G)]
        (F : CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uR} R)),
      letI : HasExt.{wRep} (SmoothRep.{max u (v + 1) uR, z, max u (v + 1) uR} R G) :=
        hasExt_of_hasDerivedCategory _
      let D := DerivedCategory.Plus.ι.obj
        ((compactProbeQuasiEtaleGSheafGlobalComplex.{u, v, uR} ρ R).obj F)
      let A := trivialSmoothRep R G
      ∃ hs : ∀ q : ℕ, IsSmooth (restrictedCohomologyAction.{u, v, uR} ρ R q F),
        (∀ p q : ℕ, Nonempty (((spectralSequence D A).page 2).X ((p : ℤ), (q : ℤ)) ≃+
          Abelian.Ext.{wRep} A (SmoothRep.of (restrictedCohomologyAction.{u, v, uR} ρ R q F)
            (hs q)) p)) ∧
        FirstQuadrantAbutmentStatement D A
          (fun n => AddCommGrpCat.of ((invariantCohomology.{u, v, uR} ρ R n).obj F))

/-- The paracompact comparison in Theorem 1.6.1(i) and the degreewise
and derived comparisons and spectral sequence on a compact space in
Theorem 1.6.1(ii). -/
def CompactProbeQuasiEtaleGlobalComparisonStatements : Prop :=
  (∀ (hX : T2Space (localizedSpaceFunctor.obj X)) (hρ : IsContinuousAction ρ),
      letI := compactProbe_hasFiniteEquivariantRefinements ρ hX hρ
      (ParacompactSpace (localizedSpaceFunctor.obj X) →
        ∀ q : ℕ, IsIso (restrictedSectionsComparison.{u, v, uR} ρ R q)) ∧
      (CompactSpace (localizedSpaceFunctor.obj X) →
        (∀ q : ℕ, IsIso (compactProbeQuasiEtaleGlobalComparison.{u, v, uR} ρ R q)) ∧
        ∀ [HasDerivedCategory.{wRep} (SmoothRep.{max u (v + 1) uR, z, max u (v + 1) uR} R G)]
          [HasDerivedCategory.{wMod} (ModuleCat.{max u (v + 1) uR} R)],
          IsIso (globalDerivedComparison.{u, v, uR} ρ R))) ∧
    CompactProbeQuasiEtaleSpectralSequenceStatement.{u, v, uR, z, wRep} ρ R

end Langlands.Cohomology.AnalyticCompactProbeGlobalComparison
