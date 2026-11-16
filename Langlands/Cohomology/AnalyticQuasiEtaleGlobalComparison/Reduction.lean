import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.DegreeZero
import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.RestrictedInjectivesStatement
import Langlands.Cohomology.ExactBaseChange.InjectiveAcyclic

/-! # Compact quasi-étale comparison from restricted-injective acyclicity -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)} {G : Type z} [Group G]
variable [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
variable (ρ : G →* Aut X)
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements (twistedQuasiEtaleTopology ρ)]
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- The compact quasi-étale comparison follows from acyclicity of the restrictions
of injective quasi-étale `G`-sheaves. -/
theorem analyticQuasiEtaleGlobalComparison_of_restrictedInjectivesAcyclic
    (h : QuasiEtaleRestrictedInjectivesAcyclicStatement.{u, v, uL, z} X G ρ R) :
    AnalyticQuasiEtaleGlobalComparisonStatement.{u, v, uL, z} X G ρ R := by
  intro hX hρ q
  have := quasiEtale_hasSheafify.{u, v, uL} X R
  have := twistedQuasiEtale_hasSheafify.{u, v, uL} X ρ R
  have := twistedQuasiEtale_enoughInjectives.{u, v, uL} X ρ R
  have := quasiEtale_enoughInjectives.{u, v, uL} X R
  have := Cohomology.DivisibleSystem.Analytic.quasiEtale_hasPointwiseRightKanExtension.{u, v, uL}
    ρ R
  have := quasiEtaleGSheafSections_preservesFiniteLimits.{u, v, uL} ρ R
  have := quasiEtaleGSheafRestriction_additive.{u, v, uL} ρ R
  have := quasiEtaleGSheafRestriction_preservesFiniteLimits.{u, v, uL} ρ R
  have := quasiEtaleGSheafRestriction_preservesFiniteColimits.{u, v, uL} ρ R
  have := isIso_quasiEtaleGlobalInclusion.{u, v, uL, z} ρ R hX hρ
  exact ExactBaseChange.isIso_baseChangeNatTrans_of_injective_acyclic
    (quasiEtaleGlobalInclusion.{u, v, uL} ρ R)
    (fun I _ r => h hX hρ I inferInstance r) q

/-- The comparison natural isomorphism supplied by restricted-injective acyclicity.
Its forward map is the published derived comparison. -/
def quasiEtaleComparisonIsoOfRestrictedInjectivesAcyclic
    (h : QuasiEtaleRestrictedInjectivesAcyclicStatement.{u, v, uL, z} X G ρ R)
    (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ) (q : ℕ) :
    quasiEtaleGSheafCohomology.{u, v, uL} ρ R q ⋙ smoothForget R G ≅
      quasiEtaleGSheafRestriction.{u, v, uL} ρ R ⋙ quasiEtaleCohomology.{u, v, uL} X R q :=
  haveI := analyticQuasiEtaleGlobalComparison_of_restrictedInjectivesAcyclic ρ R h hX hρ q
  asIso (quasiEtaleComparison.{u, v, uL} ρ R q)

@[simp]
theorem quasiEtaleComparisonIsoOfRestrictedInjectivesAcyclic_hom
    (h : QuasiEtaleRestrictedInjectivesAcyclicStatement.{u, v, uL, z} X G ρ R)
    (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ) (q : ℕ) :
    (quasiEtaleComparisonIsoOfRestrictedInjectivesAcyclic ρ R h hX hρ q).hom =
      quasiEtaleComparison.{u, v, uL} ρ R q :=
  rfl

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
