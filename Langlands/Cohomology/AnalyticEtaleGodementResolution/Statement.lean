import Langlands.Sheaf.Equivariant.AnalyticEtaleGodement
import Langlands.Sheaf.Godement.ExactnessStatement

/-!
# Exact compact-acyclic Godement resolutions on the analytic étale site

This states the analytic étale form of the exactness and acyclicity used in
Berkovich, §1.5, and in Harris 1999, §2. The functors and their coaugmentation
are the actual locally discrete point-product construction and its iterated
cokernels.
-/

noncomputable section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

namespace Langlands.Cohomology

universe u v uL z

/-- In the analytic étale model, the Godement term functors are additive and
exact, the augmented complex resolves the sheaf, and its terms are acyclic
for ordinary and smooth compactly supported sections. -/
def AnalyticEtaleGodementResolutionStatements
    {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (L : Type uL) [NormedField L] [NormedAlgebra K L]
    (X : LocalizedCategory.{u, v, v} (K := K))
    (G : Type z) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Small.{max u (v + 1) uL} G] (ρ : G →* Aut X)
    (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]
    (R : Type (max u (v + 1) uL)) [CommRing R] : Prop :=
  T2Space (localizedSpaceFunctor.obj X) → Function.Surjective (pointProjection L X) →
    IsContinuousAction ρ →
      haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
      let C₀ := etaleGodementZeroFunctor L ρ h R
      let η := etaleGodementCoaugmentation L ρ h R
      (∀ m : ℕ,
        let Cₘ := CokernelComplex.term C₀ η m
        Cₘ.Additive ∧ PreservesFiniteLimits Cₘ ∧ PreservesFiniteColimits Cₘ) ∧
      ∀ F : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R),
        QuasiIso (CokernelComplex.augmentationMap C₀ η F) ∧
        ∀ m q : ℕ,
          let CₘF := (CokernelComplex.complex C₀ η F).X m
          IsZero ((etaleCompactCohomology L h R (q + 1)).obj
            ((etaleGSheafRestriction.{u, v, uL} ρ R).obj CₘF)) ∧
          IsZero ((etaleGSheafCompactCohomology L ρ h R (q + 1)).obj CₘF)

end Langlands.Cohomology
