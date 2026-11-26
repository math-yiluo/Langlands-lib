import Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.PointFibersJointlyFaithful
import Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic.GodementCompactAcyclicProof

/-! # Acyclicity of restricted injective analytic étale `G`-sheaves

The proof of `AnalyticEtaleRestrictedInjectiveAcyclicStatement`: the Godement reduction
`analyticEtaleRestrictedInjectiveAcyclic_of_godement` applied to the joint faithfulness of
the field-valued point fibres and to the compact acyclicity of the restricted degree-zero
equivariant Godement terms. Neither analytic equivariant comparison is used.
-/

namespace Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic

open _root_.CategoryTheory
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.Equivariant.Analytic

universe u v uL z

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable (X : LocalizedCategory.{u, v, v} (K := K))
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable (G : Type z) [Group G] [TopologicalSpace G] (ρ : G →* Aut X)
variable (R : Type (max u (v + 1) uL)) [CommRing R]

/-- On Hausdorff `X` with surjective `L`-point projection and a continuous action, the
restriction of an injective étale `G`-sheaf has vanishing positive compactly supported
cohomology, and, when `|X|` is moreover compact, vanishing positive ordinary étale
cohomology. -/
theorem analyticEtaleRestrictedInjectiveAcyclic
    [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G]
    [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)] :
    AnalyticEtaleRestrictedInjectiveAcyclicStatement L X h G ρ R :=
  analyticEtaleRestrictedInjectiveAcyclic_of_godement L X h R G ρ
    (analyticEtalePointFibersJointlyFaithful L X h R)
    (analyticEtaleGodementCompactAcyclic L X h R G ρ)

end Langlands.Cohomology.AnalyticEtaleRestrictedInjectiveAcyclic
