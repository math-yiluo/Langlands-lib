import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology
import Langlands.Sheaf.Equivariant.TwistedExactGodement
import Mathlib.CategoryTheory.Retract

/-!
# Godement constructions for analytic étale `G`-sheaves

The generic coreflective Godement construction specializes to the actual category of
analytic étale `G`-sheaves. Monicity remains conditional on joint faithfulness of the
chosen field-valued points. A monic coaugmentation splits on an injective object,
and the resulting retraction transports acyclicity from its Godement term.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G]
variable (ρ : G →* Aut X)
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]
variable [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- The analytic point family, with its index lifted to the universe of the
point fibers and coefficients used by the generic Godement construction. -/
abbrev etaleGodementPoints
    (x : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X)) :
    (etaleTopology X).Point.{max u (v + 1) uL} :=
  etalePoints L h x.down

/-- Include an étale `G`-sheaf in the twisted site, apply degree-zero Godement,
and take its locally discrete part. -/
def etaleGodementZeroFunctor :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) ⥤
      EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactZeroFunctor ρ (etaleTopology X) (etaleGodementPoints L h) R
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ _)
    (LocalActionSystem.smoothCoreflector (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ))

/-- The natural coaugmentation into the degree-zero Godement term. -/
def etaleGodementCoaugmentation :
    𝟭 (EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) ⟶
      etaleGodementZeroFunctor L ρ h R :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  exactCoaugmentation ρ (etaleTopology X) (etaleGodementPoints L h) R
    (LocalActionSystem.smoothAdjunction (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ))

/-- Joint faithfulness of the chosen point fibers makes the coaugmentation monic. -/
theorem mono_etaleGodementCoaugmentation_of_jointlyFaithful
    (hpoints : JointlyFaithful
      (fun x => (etalePoints L h x).sheafFiber (A := ModuleCat.{max u (v + 1) uL} R)))
    (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) :
    Mono ((etaleGodementCoaugmentation L ρ h R).app F) := by
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  have hpoints' : JointlyFaithful
      (fun x => (etaleGodementPoints L h x).sheafFiber
        (A := ModuleCat.{max u (v + 1) uL} R)) := by
    constructor
    intro E F f g hfg
    exact hpoints.map_injective (fun x => hfg ⟨x⟩)
  exact mono_exactCoaugmentation_of_jointlyFaithful ρ (etaleTopology X) (etaleGodementPoints L h) R
    (LocalActionSystem.smoothAdjunction (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ))
    hpoints' F

/-- An injective étale `G`-sheaf is a retract of its degree-zero Godement term when its
coaugmentation is monic. -/
def etaleGodementRetractOfInjective
    (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I]
    (hmono : Mono ((etaleGodementCoaugmentation L ρ h R).app I)) :
    Retract I ((etaleGodementZeroFunctor L ρ h R).obj I) :=
  haveI := hmono
  { i := (etaleGodementCoaugmentation L ρ h R).app I
    r := Injective.factorThru (𝟙 I) ((etaleGodementCoaugmentation L ρ h R).app I)
    retract := Injective.comp_factorThru _ _ }

/-- Acyclicity of the restricted Godement term descends to an equivariantly injective
retract, for compactly supported cohomology in the indicated degree. -/
theorem isZero_etaleCompactCohomology_restriction_of_godementZero
    (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I]
    (hmono : Mono ((etaleGodementCoaugmentation L ρ h R).app I)) (q : ℕ)
    (hzero : IsZero ((etaleCompactCohomology L h R q).obj
      ((etaleGSheafRestriction.{u, v, uL} ρ R).obj
        ((etaleGodementZeroFunctor L ρ h R).obj I)))) :
    IsZero ((etaleCompactCohomology L h R q).obj
      ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I)) := by
  let e := (etaleGodementRetractOfInjective L ρ h R I hmono).map
    (etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCompactCohomology L h R q)
  exact IsZero.of_mono e.i hzero

/-- The same retraction transfers vanishing of ordinary étale cohomology. -/
theorem isZero_etaleCohomology_restriction_of_godementZero
    (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I]
    (hmono : Mono ((etaleGodementCoaugmentation L ρ h R).app I)) (q : ℕ)
    (hzero : IsZero ((etaleCohomology.{u, v, uL} X R q).obj
      ((etaleGSheafRestriction.{u, v, uL} ρ R).obj
        ((etaleGodementZeroFunctor L ρ h R).obj I)))) :
    IsZero ((etaleCohomology.{u, v, uL} X R q).obj
      ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I)) := by
  let e := (etaleGodementRetractOfInjective L ρ h R I hmono).map
    (etaleGSheafRestriction.{u, v, uL} ρ R ⋙ etaleCohomology.{u, v, uL} X R q)
  exact IsZero.of_mono e.i hzero

end Langlands.Sheaf.Equivariant.Analytic
