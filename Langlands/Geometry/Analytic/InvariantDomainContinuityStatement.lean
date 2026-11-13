import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Invariant analytic domains of `G`-spaces are `G`-spaces -/

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

/-- Let `X` be a `G`-space and `D` an analytic domain of `X` that every element of `G` maps into
itself. Then the restricted action of `G` on `D` is continuous in Berkovich's sense. -/
def InvariantDomainContinuityStatement : Prop :=
  ∀ (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
    (G : Type z) [Group G] [TopologicalSpace G] (X : GSpace.{u, v, w} K G)
    (D : (presentationOf X.obj.V).AnalyticDomain) (hD : IsInvariantDomain X.obj D),
    IsContinuousAction (invariantDomainAction X.obj D hD).ρAut

end Langlands.Analytic.SaturatedAtlasPresentation
