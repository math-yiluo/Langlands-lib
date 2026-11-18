import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactTupleCochainModels
import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactCechAcyclic
import Langlands.Sheaf.Equivariant.AnalyticQuasiEtaleLocalBijectivity

/-! # Compact quasi-etale comparison from tuple cones and lift compatibility -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology.SiteCech

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Small.{max u (v + 1) uL} G]
variable (ρ : G →* Aut X)
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]
variable (R : Type (max u (v + 1) uL)) [CommRing R]

section OrdinaryInstances

variable [LocallySmall.{max u (v + 1) uL} (QuasiEtaleSite X)]
variable [HasSheafify (quasiEtaleTopology X) (ModuleCat.{max u (v + 1) uL} R)]
variable [(quasiEtaleTopology X).WEqualsLocallyBijective (ModuleCat.{max u (v + 1) uL} R)]

/-- The actual compatible-cover Cech system is Hom-acyclic on restrictions of
injective coefficients, under the two explicit geometric inputs. -/
theorem homAcyclic_of_compactTupleCones
    (hCones : CompactCompatibleTupleConesStatement ρ)
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ)
    (I : QuasiEtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) [Injective I] :
    (compactCompatibleCechSystem ρ R hCones.cechPresentation).HomAcyclic R
      ((quasiEtaleGSheafRestriction.{u, v, uL} ρ R).obj I) := by
  intro i cover n
  classical
  choose t ht hcompact hlift using hCones i cover
  exact exactAt_of_compactTupleCones.{u, v, uL, z} ρ R cover.cover
    (fun k α => ⟨(t k α).pt, hcompact k α, hlift k α⟩)
    t (fun k α => Classical.choice (ht k α)) (fun _ _ => Iso.refl _) hC I n

end OrdinaryInstances

/-- The entire published comparison follows from compact lifted tuple cones
and compact-lift compatibility, with all ordinary site instances supplied. -/
theorem analyticQuasiEtaleGlobalComparison_of_compactTupleCones
    (hCones : CompactCompatibleTupleConesStatement ρ)
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ) :
    AnalyticQuasiEtaleGlobalComparisonStatement.{u, v, uL, z} X G ρ R := by
  have := quasiEtaleSite_locallySmall_points.{u, v, uL} X
  have := quasiEtale_hasSheafify.{u, v, uL} X R
  have := quasiEtale_enoughInjectives.{u, v, uL} X R
  have := quasiEtale_wEqualsLocallyBijective.{u, v, uL} X R
  apply analyticQuasiEtaleGlobalComparison_of_compactCompatibleCech.{u, v, uL, z}
    ρ R hCones.cechPresentation
  intro _ _ I hI
  have : Injective I := hI
  exact homAcyclic_of_compactTupleCones.{u, v, uL, z} ρ R hCones hC I

/-- The actual natural comparison isomorphism constructed from the two
explicit geometric inputs. Its forward map is the published comparison. -/
def quasiEtaleComparisonIsoOfCompactTupleCones
    (hCones : CompactCompatibleTupleConesStatement ρ)
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ)
    (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ) (q : ℕ) :
    quasiEtaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G ≅
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ quasiEtaleCohomology.{u, v, uL} X R q :=
  haveI := analyticQuasiEtaleGlobalComparison_of_compactTupleCones.{u, v, uL, z}
    ρ R hCones hC hX hρ q
  asIso (quasiEtaleComparison.{u, v, uL} ρ R q)

@[simp]
theorem quasiEtaleComparisonIsoOfCompactTupleCones_hom
    (hCones : CompactCompatibleTupleConesStatement ρ)
    (hC : HasCompatibleCompactQuasiEtaleLifts ρ)
    (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ) (q : ℕ) :
    (quasiEtaleComparisonIsoOfCompactTupleCones.{u, v, uL, z}
      ρ R hCones hC hX hρ q).hom = quasiEtaleComparison.{u, v, uL} ρ R q := rfl

/-- The two remaining published geometric propositions suffice for the exact
comparison target. Compactness supplies the Hausdorff input to compatibility. -/
theorem analyticQuasiEtaleGlobalComparison_of_tupleCones_liftCompatibilityStatement
    (hCones : CompactCompatibleTupleConesStatement ρ)
    (hKL : QuasiEtaleLiftCompatibilityStatement.{u, v, z} K) :
    AnalyticQuasiEtaleGlobalComparisonStatement.{u, v, uL, z} X G ρ R := by
  intro hX hρ q
  exact analyticQuasiEtaleGlobalComparison_of_compactTupleCones.{u, v, uL, z}
    ρ R hCones
    (hasCompatibleCompactQuasiEtaleLifts_of_compatibilityStatement hKL hX.2 hρ)
    hX hρ q

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
