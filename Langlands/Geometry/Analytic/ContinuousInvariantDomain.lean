import Langlands.Geometry.Analytic.NearIdentityDomainRestriction

/-! # Continuous actions on invariant analytic domains -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G]

/-- Restriction to an invariant analytic domain preserves Berkovich continuity,
even without a Hausdorff hypothesis on the ambient analytic space. -/
theorem IsContinuousAction.invariantDomainAction
    {X : Action (LocalizedCategory.{u, v, w} (K := K)) G}
    (hX : IsContinuousAction X.ρAut)
    (D : (presentationOf X.V).AnalyticDomain) (hD : IsInvariantDomain X D) :
    IsContinuousAction (invariantDomainAction X D hD).ρAut := by
  intro τ
  apply Filter.mem_of_superset (hX τ.ambient)
  intro g hg
  exact IsNear.domainRestrict_id D τ (X.ρ g) (hD g) hg

namespace GSpace

/-- An invariant analytic domain with its canonical continuous restricted action. -/
def invariantDomain (X : GSpace.{u, v, w} K G)
    (D : (presentationOf X.obj.V).AnalyticDomain) (hD : IsInvariantDomain X.obj D) :
    GSpace.{u, v, w} K G :=
  invariantDomainGSpace X D hD (X.property.2.invariantDomainAction D hD)

/-- The canonical equivariant inclusion of an invariant domain, as a map of G-spaces. -/
def invariantDomainInclusion (X : GSpace.{u, v, w} K G)
    (D : (presentationOf X.obj.V).AnalyticDomain) (hD : IsInvariantDomain X.obj D) :
    invariantDomain X D hD ⟶ X :=
  invariantDomainGSpaceInclusion X D hD (X.property.2.invariantDomainAction D hD)

@[simp]
theorem invariantDomain_obj (X : GSpace.{u, v, w} K G)
    (D : (presentationOf X.obj.V).AnalyticDomain) (hD : IsInvariantDomain X.obj D) :
    (invariantDomain X D hD).obj = invariantDomainAction X.obj D hD := rfl

@[simp]
theorem invariantDomainInclusion_hom (X : GSpace.{u, v, w} K G)
    (D : (presentationOf X.obj.V).AnalyticDomain) (hD : IsInvariantDomain X.obj D) :
    (invariantDomainInclusion X D hD).hom.hom = domainι X.obj.V D := rfl

end GSpace

end Langlands.Analytic.SaturatedAtlasPresentation
