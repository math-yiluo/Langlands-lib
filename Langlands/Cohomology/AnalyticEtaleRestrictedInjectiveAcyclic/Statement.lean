import Langlands.Sheaf.Equivariant.AnalyticEtaleCohomology

/-!
# Acyclicity of restricted injective étale `G`-sheaves

Internal prerequisite statements for the compactly supported comparison and, on compact
spaces, the ordinary comparison. These statements assert vanishing for `b^* I`, where `I`
is injective among étale `G`-sheaves; they do not assert that `b^* I` is injective.
-/

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open CategoryTheory CategoryTheory.Limits
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (G : Type z) [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- On Hausdorff `X`, restriction of an injective étale `G`-sheaf is acyclic for compactly
supported sections, with supports measured using the given `L`-valued points. -/
def AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement
    [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)] : Prop :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  T2Space (localizedSpaceFunctor.obj X) → Function.Surjective (pointProjection L X) →
    IsContinuousAction ρ →
      ∀ (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (_ : Injective I) (q : ℕ),
        IsZero ((etaleCompactCohomology L h R (q + 1)).obj
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I))

/-- On compact Hausdorff `X`, restriction of an injective étale `G`-sheaf is acyclic for
ordinary global sections. The point hypotheses are retained from the compact comparison. -/
def AnalyticEtaleRestrictedInjectiveGlobalAcyclicStatement
    [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)] : Prop :=
  haveI := twistedEtale_hasSheafify.{u, v, uL} X ρ R
  T2Space (localizedSpaceFunctor.obj X) → CompactSpace (localizedSpaceFunctor.obj X) →
    Function.Surjective (pointProjection L X) → IsContinuousAction ρ →
      ∀ (I : EtaleGSheaf ρ (ModuleCat.{max u (v + 1) uL} R)) (_ : Injective I) (q : ℕ),
        IsZero ((etaleCohomology.{u, v, uL} X R (q + 1)).obj
          ((etaleGSheafRestriction.{u, v, uL} ρ R).obj I))

/-- The compactly supported and compact-space global acyclicity prerequisites together. -/
def AnalyticEtaleRestrictedInjectiveAcyclicStatement
    [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)] : Prop :=
  AnalyticEtaleRestrictedInjectiveCompactAcyclicStatement L X h G ρ R ∧
    AnalyticEtaleRestrictedInjectiveGlobalAcyclicStatement L X G ρ R

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
