import Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison.CompactCompatibleCovers
import Mathlib.CategoryTheory.Limits.Shapes.WidePullbacks

/-! # Compact lifted tuple cones for compatible quasi-étale covers -/

noncomputable section

namespace Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant Langlands.Sheaf.Equivariant.Analytic
open Langlands.Cohomology.SiteCech

universe u v z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable {G : Type z} [Group G] [TopologicalSpace G]
variable (ρ : G →* Aut X)

/-- The missing geometric existence assertion: every nonempty finite tuple of
a compatible compact cover has an actual limiting cone whose point is compact
and admits a continuous local lift of the base action. -/
def CompactCompatibleTupleConesStatement : Prop :=
  ∀ i (c : CompactCompatibleCover ρ i) (n : ℕ)
    (α : Fin (n + 1) → Fin c.cover.size),
    ∃ t : WidePullbackCone (fun j => c.cover.arrow (α j)),
      Nonempty (IsLimit t) ∧ IsCompactSpace t.pt.left ∧
        Nonempty (ActionLift ρ t.pt.hom)

end Langlands.Cohomology.AnalyticQuasiEtaleGlobalComparison
