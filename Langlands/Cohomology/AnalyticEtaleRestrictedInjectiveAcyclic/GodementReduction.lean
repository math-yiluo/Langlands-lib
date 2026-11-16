import Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.Statement
import Langlands.Sheaf.Equivariant.AnalyticEtaleGodement
import Langlands.Sheaf.Equivariant.AnalyticEtaleCompactGlobal

/-!
# Analytic inputs to restricted-injective acyclicity

The remaining geometric inputs are stated separately. The proved reduction uses the
published Godement retraction and, on compact spaces, the derived inclusion of compact
sections in all sections. Neither analytic equivariant comparison is assumed.
-/

noncomputable section

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The actual field-valued point fibers detect morphisms of all étale module sheaves.
This is a geometric input, stronger than detection of sections over `etaleSelf X`. -/
def AnalyticEtalePointFibersJointlyFaithfulStatement : Prop :=
  T2Space (localizedSpaceFunctor.obj X) →
    Function.Surjective (pointProjection L X) →
      JointlyFaithful
        (fun x => (etalePoints L h x).sheafFiber
          (A := ModuleCat.{max u (v + 1) uL} R))

variable (G : Type z) [Group G] [TopologicalSpace G] (ρ : G →* Aut X)

/-- Positive-degree compact-support vanishing for the restriction of every degree-zero
equivariant Godement term. This assertion is an unproved analytic input. -/
def AnalyticEtaleGodementCompactAcyclicStatement
    [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)] : Prop :=
  T2Space (localizedSpaceFunctor.obj X) → Function.Surjective (pointProjection L X) →
    IsContinuousAction ρ →
      ∀ (F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (q : ℕ),
        IsZero ((etaleCompactCohomology L h R (q + 1)).obj
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj
            ((etaleGodementZeroFunctor L ρ h R).obj F)))

variable [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- Compact-support acyclicity supplies both required assertions. The global part uses
the given `h` through the compact/global isomorphism, although its target does not bind `h`. -/
theorem analyticEtaleRestrictedInjectiveAcyclic_of_compact
    (hc : AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R) :
    AnalyticEtaleRestrictedInjectiveAcyclicStatement L X h G ρ R := by
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  refine ⟨hc, ?_⟩
  intro hT2 hcompact hX hcontinuous I hI q
  let := hcompact
  exact (isZero_etaleCompactCohomology_iff_of_compactSpace L h R hX (q + 1)
    ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I)).mp
      (hc hT2 hX hcontinuous I hI q)

/-- The conjunction of compact and compact-space ordinary acyclicity is equivalent to
its compact-support component when the supplied point axioms are retained. -/
theorem analyticEtaleRestrictedInjectiveAcyclic_iff_compact :
    AnalyticEtaleRestrictedInjectiveAcyclicStatement L X h G ρ R ↔
      AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R :=
  ⟨And.left, analyticEtaleRestrictedInjectiveAcyclic_of_compact L X h R G ρ⟩

/-- Joint faithfulness makes the Godement coaugmentation monic. Injectivity splits it,
so compact-support vanishing of the Godement term passes to the restricted sheaf. -/
theorem analyticEtaleRestrictedInjectiveAcyclic_of_godement
    (hpoints : AnalyticEtalePointFibersJointlyFaithfulStatement L X h R)
    (hgodement : AnalyticEtaleGodementCompactAcyclicStatement L X h R G ρ) :
    AnalyticEtaleRestrictedInjectiveAcyclicStatement L X h G ρ R := by
  have := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  apply analyticEtaleRestrictedInjectiveAcyclic_of_compact L X h R G ρ
  intro hT2 hX hcontinuous I hI q
  let := hI
  exact isZero_etaleCompactCohomology_restriction_of_godementZero L ρ h R I
    (mono_etaleGodementCoaugmentation_of_jointlyFaithful L ρ h R
      (hpoints hT2 hX) I) (q + 1) (hgodement hT2 hX hcontinuous I q)

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
