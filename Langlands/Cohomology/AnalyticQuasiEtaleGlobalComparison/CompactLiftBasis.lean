import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.DegreeZero
import Langlands.Cohomology.SiteCech.FiniteCoverLifting
import Langlands.Sheaf.Equivariant.AnalyticCommonSubgroupRefinements

/-! # Finite ordinary refinements on compact objects admitting action lifts -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Sheaf.Equivariant.TwistedOver
open Langlands.Cohomology.SiteCech

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)

/-- Compact ordinary quasi-étale objects on which the action admits a lift. -/
def CompactLiftBasis :=
  {U : QuasiEtaleSite X // IsCompactSpace U.left ∧ Nonempty (ActionLift ρ U.hom)}

/-- The ordinary site object represented by a compact object admitting a lift. -/
def compactLiftBasisObject (i : CompactLiftBasis ρ) : QuasiEtaleSite X :=
  i.val

/-- For a compact space with continuous action, the identity belongs to the
family of compact objects admitting action lifts. -/
def compactLiftBasisIdentity (hX : IsCompactSpace X) (hρ : IsContinuousAction ρ) :
    CompactLiftBasis ρ :=
  ⟨MorphismProperty.Over.mk ⊤ (𝟙 X) (quasiEtale.id_mem X), hX,
    ⟨identityActionLift ρ hρ⟩⟩

variable [IsTopologicalGroup G]
variable [(compactLiftSystem ρ).HasFiniteEquivariantRefinements
  (twistedQuasiEtaleTopology ρ)]

/-- The authorized finite equivariant refinements supply finite ordinary
refinements within the compact objects admitting lifts. -/
theorem hasFiniteBasisCoverRefinements_compactLiftBasis :
    HasFiniteBasisCoverRefinements (quasiEtaleTopology X) (compactLiftBasisObject ρ) := by
  intro i S hS
  obtain ⟨l⟩ := i.property.2
  have ha : (compactLiftSystem ρ).IsAdmissible ((ι quasiEtale ρ).obj i.val)
      (liftOpenSubgroup (U := (ι quasiEtale ρ).obj i.val) l)
      (liftAction (U := (ι quasiEtale ρ).obj i.val) l) := by
    refine ⟨i.property.1, l, le_rfl, ?_⟩
    ext g
    rfl
  obtain ⟨d⟩ := nonempty_commonSubgroupRefinement
    (fun U : QuasiEtaleSite X => IsCompactSpace U.left) (fun _ _ h => h)
    (quasiEtaleTopology X) ha hS
  exact ⟨{
    size := d.size
    index := fun j => ⟨d.obj j, d.admissible j, ⟨d.lift j⟩⟩
    arrow := d.arrow
    covering := d.covering
  }, d.mem⟩

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
