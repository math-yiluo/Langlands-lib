import Langlands.Geometry.Analytic.SaturatedComparisonEquivalence
import Langlands.Geometry.Analytic.AnalyticDomainSpaces
import Langlands.Geometry.Analytic.StrongAtlasComposition

/-! # Chart-domain inclusions into original compatible presentations -/

noncomputable section

universe u v

namespace Langlands.Analytic.AffinoidAtlasPresentation

open Set IndexedAffinoidAtlas SaturatedAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, v} K) (S : A.atlas.localDomainFamily)

/-- The chart domain in the saturated atlas, retaining the algebra of the
chosen local-domain representative as its whole chart. -/
abbrev saturatedChartDomain : TopChartPresentation.{u, v, v} K :=
  TopChartPresentation.ofChart A.saturatedPresentation S

/-- The chart-domain inclusion into the original atlas. The source and the
intermediate saturated presentation supply compatible bounded pullbacks. -/
def saturatedChartDomainInclusion : CompatibleStrongHom
    (A.saturatedChartDomain S).presentation A :=
  let B := ofSaturation A
  let D := B.chartDomain S
  (CompatibleStrongHom.ofSaturated (B.domainInclusion D) (B.domain D).hasAllLocalDomains).comp
    (CompatibleStrongHom.ofSaturated A.directFromSaturation B.hasAllLocalDomains)

@[simp]
theorem saturatedChartDomainInclusion_apply (x : (A.saturatedChartDomain S).presentation.space) :
    (A.saturatedChartDomainInclusion S).baseMap x = x.val := rfl

/-- At the whole chart of the domain the inclusion lands in the chosen
representative's original parent chart. -/
theorem saturatedChartDomainInclusion_admissible :
    (A.saturatedChartDomainInclusion S).baseMap ''
      range ((A.saturatedChartDomain S).presentation.atlas.chart
        (A.saturatedChartDomain S).topChart) ⊆
      range (A.atlas.chart (A.atlas.saturatedRepresentative S).index) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨(A.atlas.saturatedRepresentative S).domain.spectrumMap x, rfl⟩

private theorem directFromSaturation_pullback_parent
    (h : A.directFromSaturation.baseMap '' range (A.saturatedPresentation.atlas.chart S) ⊆
      range (A.atlas.chart (A.atlas.saturatedRepresentative S).index)) :
    A.directFromSaturation.pullback S (A.atlas.saturatedRepresentative S).index h =
      (A.atlas.saturatedRepresentative S).domain.baseMap := by
  let U := A.atlas.saturatedRepresentative S
  let p := A.atlas.saturatedToOriginalInclusion S U.index (fun x hx => h ⟨x, hx, rfl⟩)
  let whole := PresentedAffinoidAlgebra.Domain.whole K (A.atlas.algebra U.index)
  have hwhole : A.atlas.chart U.index '' whole.locus ⊆ range (A.atlas.chart U.index) :=
    image_subset_range _ _
  have hU : U.locus ⊆ range (A.atlas.chart U.index) := image_subset_range _ _
  let r : BoundedAlgHom K (A.atlas.algebra U.index) U.algebra := p.restriction
  change r = U.domain.baseMap
  calc
    r = r.comp whole.baseMap := (BoundedAlgHom.comp_id r).symm
    _ = r.comp (A.atlas.domainChartRestriction U.index U.index whole hwhole) :=
      congrArg r.comp
        (A.atlas.domainChartRestriction_self U.index whole hwhole).symm
    _ = A.atlas.domainChartRestriction U.index U.index U.domain hU :=
      p.comp_chart U.index hU hwhole
    _ = U.domain.baseMap := A.atlas.domainChartRestriction_self U.index U.domain hU

/-- The complete bounded pullback to the whole chart is the structural map
of its represented domain over the original parent chart. -/
theorem saturatedChartDomainInclusion_pullback
    (h : (A.saturatedChartDomainInclusion S).baseMap ''
      range ((A.saturatedChartDomain S).presentation.atlas.chart
        (A.saturatedChartDomain S).topChart) ⊆
      range (A.atlas.chart (A.atlas.saturatedRepresentative S).index)) :
    (A.saturatedChartDomainInclusion S).pullback (A.saturatedChartDomain S).topChart
      (A.atlas.saturatedRepresentative S).index h =
        (A.atlas.saturatedRepresentative S).domain.baseMap := by
  let B := ofSaturation A
  let D := B.chartDomain S
  let i := (A.saturatedChartDomain S).topChart
  let I := CompatibleStrongHom.ofSaturated (B.domainInclusion D) (B.domain D).hasAllLocalDomains
  let J := CompatibleStrongHom.ofSaturated A.directFromSaturation B.hasAllLocalDomains
  let j := (A.atlas.saturatedRepresentative S).index
  have hI : I.baseMap '' range ((B.domain D).presentation.atlas.chart i) ⊆
      range (B.presentation.atlas.chart S) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hJ : J.baseMap '' range (B.presentation.atlas.chart S) ⊆ range (A.atlas.chart j) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨(A.atlas.saturatedRepresentative S).domain.spectrumMap x, rfl⟩
  refine (CompatibleStrongHom.comp_pullback I J i S j hI hJ h).trans ?_
  change (B.presentation.atlas.restriction S S Subset.rfl).comp
    (A.directFromSaturation.pullback S j hJ) = _
  erw [B.presentation.atlas.restriction_id S Subset.rfl, BoundedAlgHom.id_comp]
  exact A.directFromSaturation_pullback_parent S hJ

end Langlands.Analytic.AffinoidAtlasPresentation
