import Langlands.Sheaf.Equivariant.AnalyticCompactProbeQuasiEtale
import Langlands.Geometry.Analytic.CompactProbeQuasiEtaleCompactRefinementsProof
import Langlands.Geometry.Analytic.QuasiEtaleActionLiftProof
import Langlands.Geometry.Analytic.QuasiEtaleLiftCompatibilityProof
import Langlands.Sheaf.Equivariant.AnalyticFreeRepresentable
import Langlands.Cohomology.DivisibleSystem.AnalyticQuasiEtale
import Langlands.Sheaf.Equivariant.TwistedExactGlobalComplex

/-! # Derived global sections for the compact-probe quasi-étale topology -/

noncomputable section

universe u v uL z w w₁ w₂

namespace Langlands.Sheaf.Equivariant.Analytic

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A continuous action on a Hausdorff analytic space has finite equivariant refinements
for the compact-probe topology. Endow each member of a finite compact refinement with a
lift of the action and restrict the lifts along its arrows to common open subgroups. -/
theorem compactProbe_hasFiniteEquivariantRefinements (ρ : G →* Aut X)
    (hX : T2Space (localizedSpaceFunctor.obj X)) (hρ : IsContinuousAction ρ) :
    (compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedCompactProbeQuasiEtaleTopology ρ) := by
  have hasLifts := hasCompactQuasiEtaleLifts_of_actionLiftStatement ρ
    (quasiEtaleActionLift (K := K)) hX hρ
  have liftCompatibility := hasCompatibleCompactQuasiEtaleLifts_of_compatibilityStatement
    (quasiEtaleLiftCompatibility K) hX hρ
  constructor
  rintro U H a ⟨hU, l, hH, rfl⟩ S hS
  obtain ⟨n, V, f, hV, hf, hcover⟩ := compactProbeQuasiEtaleCompactRefinements K X hU hS
  let lift (i : Fin n) : ActionLift ρ (V i).hom := (hasLifts (hV i)).some
  refine ⟨n, fun i => (ι quasiEtale ρ).obj (V i), fun i => liftOpenSubgroup (lift i),
    fun i => liftAction (U := (ι quasiEtale ρ).obj (V i)) (lift i),
    fun i => (ι quasiEtale ρ).map (f i), fun i => ⟨hV i, lift i, le_rfl, ?_⟩, hf,
    fun i => ?_, ?_⟩
  · exact MonoidHom.ext fun _ => rfl
  · obtain ⟨N, hN, hNl, hNi, heq⟩ := liftCompatibility (f i) hU (hV i) l (lift i)
    refine isLocallyEquivariant_of_intertwines (⟨N, hN⟩ ⊓ H) inf_le_right
      (fun g hg => hNi hg.1) fun g hg => ?_
    exact hom_ext ((one_mul _).trans (mul_one _).symm) (heq g⁻¹ (inv_mem hg.1))
  · change Sieve.functorPullback (ι quasiEtale ρ) _ ∈ compactProbeQuasiEtaleTopology X U.obj
    refine (compactProbeQuasiEtaleTopology X).superset_covering ?_ hcover
    rintro W g ⟨Y, e, _, ⟨i⟩, rfl⟩
    exact ⟨_, (ι quasiEtale ρ).map e, (ι quasiEtale ρ).map (f i), ⟨i⟩,
      ((ι quasiEtale ρ).map_comp e (f i)).symm⟩

private theorem moduleSheaf_enoughInjectives {C : Type*} [Category C] [EssentiallySmall.{w} C]
    [LocallySmall.{w} C] (J : GrothendieckTopology C) (R : Type w) [CommRing R] :
    EnoughInjectives (Sheaf J (ModuleCat.{w} R)) :=
  haveI : ∀ Y : Cᵒᵖ, HasLimitsOfShape
      (StructuredArrow Y (equivSmallModel.{w} C).inverse.op) (ModuleCat.{w} R) :=
    fun _ => hasLimitsOfShape_of_essentiallySmall.{w} _ _
  haveI := hasSheafifyEssentiallySmallSite J (ModuleCat.{w} R)
  haveI := Sheaf.isGrothendieckAbelian_of_essentiallySmall.{w} J (ModuleCat.{w} R)
  IsGrothendieckAbelian.enoughInjectives

section Ordinary

variable (X) (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Sheafification of module presheaves for the compact-probe topology. -/
theorem compactProbeQuasiEtale_hasSheafify :
    HasSheafify (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := quasiEtaleSite_essentiallySmall_points.{u, v, uL} X
  hasSheafifyEssentiallySmallSite _ _

/-- Module sheaves for the compact-probe topology have enough injectives. -/
theorem compactProbeQuasiEtale_enoughInjectives :
    EnoughInjectives (Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) :=
  haveI := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  haveI := quasiEtaleSite_essentiallySmall_points.{u, v, uL} X
  moduleSheaf_enoughInjectives _ R

/-- Ordinary global sections are evaluation at the identity of the analytic space. -/
abbrev compactProbeQuasiEtaleSections := sheafSectionsModule (compactProbeQuasiEtaleTopology X) R
  (quasiEtaleSelf X)

/-- Cohomology of ordinary global sections for the compact-probe topology. -/
def compactProbeQuasiEtaleCohomology (q : ℕ) :
    Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      ModuleCat.{max u (v + 1) uL} R :=
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  sectionsDerived (compactProbeQuasiEtaleTopology X) R (quasiEtaleSelf X) q

/-- Degree zero of ordinary cohomology is the global sections functor. -/
def compactProbeQuasiEtaleCohomologyZeroIso :
    compactProbeQuasiEtaleCohomology.{u, v, uL} X R 0 ≅ compactProbeQuasiEtaleSections.{u, v, uL} X R :=
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  sectionsDerivedZeroIso (compactProbeQuasiEtaleTopology X) R (quasiEtaleSelf X)

variable [HasDerivedCategory.{w₁} (ModuleCat.{max u (v + 1) uL} R)]

/-- The ordinary derived global sections in the bounded below derived category of modules. -/
def compactProbeQuasiEtaleGlobalComplex :
    Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  sheafSectionsComplex (compactProbeQuasiEtaleTopology X) R (quasiEtaleSelf X)

/-- Cohomology of the ordinary derived global sections recovers the degreewise functor. -/
def compactProbeQuasiEtaleGlobalComplexHomologyIso
    (F : Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (ModuleCat.{max u (v + 1) uL} R) q).obj
        ((compactProbeQuasiEtaleGlobalComplex.{u, v, uL} X R).obj F) ≅
      (compactProbeQuasiEtaleCohomology.{u, v, uL} X R q).obj F :=
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  letI := HasDerivedCategory.standard
    (Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R))
  sheafSectionsComplexHomologyIso (compactProbeQuasiEtaleTopology X) R (quasiEtaleSelf X) F q

end Ordinary

section Equivariant

variable (ρ : G →* Aut X) (R : Type (max u (v + 1) uL)) [CommRing R]

/-- Restriction along untwisted arrows, with the given compact-probe topology on the ordinary site. -/
abbrev compactProbeQuasiEtaleGSheafRestriction :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      Sheaf (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R) :=
  (compactLiftSystem ρ).discreteSheafInclusion _ _ ⋙
    TwistedOver.restriction ρ (compactProbeQuasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)

/-- The smooth part of the global sections representation of a compact-probe `G`-sheaf. -/
abbrev compactProbeQuasiEtaleGSheafSections :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  discreteGlobalSections (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)

/-- The smooth sections include into the global sections of the restricted sheaf. -/
def compactProbeQuasiEtaleGlobalInclusion :
    compactProbeQuasiEtaleGSheafSections.{u, v, uL} ρ R ⋙ smoothForget R G ⟶
      compactProbeQuasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ compactProbeQuasiEtaleSections.{u, v, uL} X R :=
  smoothGlobalInclusion (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)

variable [Small.{max u (v + 1) uL} G]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Module presheaves on the twisted compact-probe site have sheafification. -/
theorem twistedCompactProbeQuasiEtale_hasSheafify :
    HasSheafify (twistedCompactProbeQuasiEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := twistedQuasiEtale_essentiallySmall_points.{u, v, uL} X ρ
  hasSheafifyEssentiallySmallSite _ _

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- The module sheaf category on the twisted compact-probe site has enough injectives. -/
theorem twistedCompactProbeQuasiEtale_enoughInjectives :
    EnoughInjectives
      (Sheaf (twistedCompactProbeQuasiEtaleTopology ρ) (ModuleCat.{max u (v + 1) uL} R)) :=
  haveI := twistedQuasiEtale_locallySmall_points.{u, v, uL} X ρ
  haveI := twistedQuasiEtale_essentiallySmall_points.{u, v, uL} X ρ
  moduleSheaf_enoughInjectives _ R

variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedCompactProbeQuasiEtaleTopology ρ)]

/-- The right derived functors of smooth global sections take values in smooth representations. -/
def compactProbeQuasiEtaleGSheafCohomology (q : ℕ) :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  discreteGlobalDerived (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ) q

/-- Degree zero of equivariant cohomology is the smooth global sections functor. -/
def compactProbeQuasiEtaleGSheafCohomologyZeroIso :
    compactProbeQuasiEtaleGSheafCohomology.{u, v, uL} ρ R 0 ≅ compactProbeQuasiEtaleGSheafSections.{u, v, uL} ρ R :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  discreteGlobalDerivedZeroIso (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ)

/-- Comparison from smooth derived global sections to cohomology of the ordinary restriction. -/
def compactProbeQuasiEtaleGlobalComparison (q : ℕ) :
    compactProbeQuasiEtaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G ⟶
      compactProbeQuasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ compactProbeQuasiEtaleCohomology.{u, v, uL} X R q :=
  haveI := compactProbeQuasiEtale_hasSheafify.{u, v, uL} X R
  haveI := compactProbeQuasiEtale_enoughInjectives.{u, v, uL} X R
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  haveI := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  globalComparison (compactProbeQuasiEtaleTopology X) R (compactLiftSystem ρ) q

variable [HasDerivedCategory.{w₂} (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G)]

/-- The derived smooth global sections as an object of the bounded below derived category
of smooth representations. -/
def compactProbeQuasiEtaleGSheafGlobalComplex :
    CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      DerivedCategory.Plus (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard
    (CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplex (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _)

/-- Cohomology of the derived smooth global sections recovers the degreewise functor. -/
def compactProbeQuasiEtaleGSheafGlobalComplexHomologyIso
    (F : CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ) :
    (DerivedCategory.Plus.homologyFunctor (SmoothRep.{max u (v + 1) uL, z, max u (v + 1) uL} R G) q).obj
        ((compactProbeQuasiEtaleGSheafGlobalComplex.{u, v, uL} ρ R).obj F) ≅
      (compactProbeQuasiEtaleGSheafCohomology.{u, v, uL} ρ R q).obj F :=
  haveI := twistedCompactProbeQuasiEtale_hasSheafify.{u, v, uL} ρ R
  haveI := twistedCompactProbeQuasiEtale_enoughInjectives.{u, v, uL} ρ R
  letI := HasDerivedCategory.standard
    (CompactProbeQuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R))
  exactGlobalComplexHomologyIso (compactProbeQuasiEtaleTopology X) R
    ((compactLiftSystem ρ).discreteSheafInclusion _ _) F q

end Equivariant

end Langlands.Sheaf.Equivariant.Analytic
