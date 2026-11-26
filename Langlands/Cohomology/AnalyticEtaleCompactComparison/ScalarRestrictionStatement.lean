import Langlands.Cohomology.DivisibleSystem.SmoothScalarExtension
import Langlands.Sheaf.Equivariant.AnalyticEtaleComparison
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.CategoryTheory.Sites.Whiskering

/-!
# Restricting constant coefficient rings in analytic compact cohomology

The constant-ring case of Berkovich, *Equish*, Corollary 1.5.2(ii).
The cohomology functors use the actual locally discrete étale site.
-/

noncomputable section

open CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Cohomology.AnalyticEtaleCompactComparison

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : LocalizedCategory.{u, v, v} (K := K)}
  {G : Type z} [Group G] [TopologicalSpace G] (ρ : G →* Aut X)

variable (R S : Type (max u (v + 1) uL)) [CommRing R] [CommRing S] [Algebra R S]

/-- Restrict the scalar action on every section of the actual étale `G`-sheaf.
The covers of local discreteness persist because the section functions
and their stabilizers are the same. -/
def etaleGSheafRestrictScalars :
    EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} S) ⥤
      EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R) :=
  (distinguishedLiftSystem ρ).smoothSheafProperty _ (twistedEtaleTopology ρ) |>.lift
    ((distinguishedLiftSystem ρ).smoothSheafInclusion _ (twistedEtaleTopology ρ) ⋙
      sheafCompose (twistedEtaleTopology ρ) (ModuleCat.restrictScalars (algebraMap R S)))
    (fun F => F.property)

variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
  (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
  [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
  [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- Restriction of a constant coefficient ring commutes with both actual
compact cohomology functors, retaining the smooth action for `X{G}`. -/
def AnalyticEtaleCompactScalarRestrictionStatement : Prop :=
  T2Space (localizedSpaceFunctor.obj X) → Function.Surjective (pointProjection L X) →
  IsContinuousAction ρ → ∀ q : ℕ,
    Nonempty (etaleGSheafCompactCohomology L ρ h S q ⋙
        smoothRepRestrictScalars.{max u (v + 1) uL} R S G ≅
      etaleGSheafRestrictScalars.{u, v, uL} ρ R S ⋙ etaleGSheafCompactCohomology L ρ h R q) ∧
    Nonempty (etaleGSheafInvariantCompactCohomology L ρ h S q ⋙
        ModuleCat.restrictScalars (algebraMap R S) ≅
      etaleGSheafRestrictScalars.{u, v, uL} ρ R S ⋙
        etaleGSheafInvariantCompactCohomology L ρ h R q)

end Langlands.Cohomology.AnalyticEtaleCompactComparison
