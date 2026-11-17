import Langlands.Geometry.Analytic.FibreProductLocalAtlas
import Langlands.Geometry.Analytic.SaturatedAffinoidAtlas
import Langlands.Geometry.Analytic.AffinoidIdempotents

/-! # Original pair algebras as actual full domains of the local product atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FibreProduct

open CategoryTheory Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation
open IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-- The original entire range restriction represents the exact inverse
image of a raw pair chart, including an empty chart image. -/
theorem rangeRestriction_represents {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    Represents K (rangeRestriction f g h)
      ((chartSystem f g).chart q ⁻¹' range ((chartSystem f g).chart p)) := by
  have hr : range (BanachSpectrum.comap (rangeRestriction f g h).toBoundedRingHom) =
      (chartSystem f g).chart q ⁻¹' range ((chartSystem f g).chart p) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨y, (chart_rangeRestriction f g h y).symm⟩
    · rintro ⟨y, hy⟩
      exact ⟨y, (chartSystem f g).chart_injective q
        ((chart_rangeRestriction f g h y).trans hy)⟩
  refine ⟨hr ▸ (isCompact_range
    (BanachSpectrum.comapContinuous (rangeRestriction f g h).toBoundedRingHom).continuous).isClosed,
    hr, ?_⟩
  exact fun T φ hφ => rangeRestriction_universal f g h T φ hφ

/-- The raw pair algebra is unchanged in this actual full-domain
representation over the chosen containing raw pair. -/
def rangeDomain {p q : PairIndex f g}
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    Domain K (algebra f g q) where
  algebra := algebra f g p
  baseMap := rangeRestriction f g h
  locus := (chartSystem f g).chart q ⁻¹' range ((chartSystem f g).chart p)
  represents := rangeRestriction_represents f g h

variable [Nonempty (LocalAtlasIndex f g)]

theorem exists_goodPairContainer (p : PairIndex f g) (hp : p ∈ goodPairs f g) :
    ∃ T : LocalAtlasIndex f g,
      range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart T.rep) ∧
        ((range ((chartSystem f g).chart p)).Nonempty →
          range ((chartSystem f g).chart T.rep) = range ((chartSystem f g).chart p)) := by
  classical
  by_cases hne : (range ((chartSystem f g).chart p)).Nonempty
  · exact ⟨⟨range ((chartSystem f g).chart p), hne, p, hp, rfl⟩,
      (LocalAtlasIndex.range_rep
        (⟨range ((chartSystem f g).chart p), hne, p, hp, rfl⟩ : LocalAtlasIndex f g)).symm.subset,
      fun _ => LocalAtlasIndex.range_rep _⟩
  · exact ⟨Classical.choice inferInstance, (fun x hx => (hne ⟨x, hx⟩).elim),
      fun h => (hne h).elim⟩

/-- A nonempty good pair is an original chart range. An empty pair can
instead be represented as a full domain of any existing original chart. -/
def goodPairContainer (p : PairIndex f g) (hp : p ∈ goodPairs f g) :
    LocalAtlasIndex f g :=
  Classical.choose (exists_goodPairContainer f g p hp)

theorem range_subset_goodPairContainer (p : PairIndex f g) (hp : p ∈ goodPairs f g) :
    range ((chartSystem f g).chart p) ⊆
      range ((chartSystem f g).chart (goodPairContainer f g p hp).rep) := by
  exact (Classical.choose_spec (exists_goodPairContainer f g p hp)).1

theorem range_goodPairContainer_of_nonempty (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (hne : (range ((chartSystem f g).chart p)).Nonempty) :
    range ((chartSystem f g).chart (goodPairContainer f g p hp).rep) =
      range ((chartSystem f g).chart p) :=
  (Classical.choose_spec (exists_goodPairContainer f g p hp)).2 hne

variable (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
  (hC : C.atlas.HasAllLocalDomains)

/-- Every good raw pair, even an empty one, is an actual local full
domain of the already constructed original local product atlas. -/
def goodPairLocalDomain (p : PairIndex f g) (hp : p ∈ goodPairs f g) :
    LocalDomain (localAtlas f g hA hB hC) :=
  ⟨goodPairContainer f g p hp, rangeDomain f g (range_subset_goodPairContainer f g p hp)⟩

theorem goodPairLocalDomain_ambientMap (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (x : BanachSpectrum (algebra f g p)) :
    (goodPairLocalDomain f g hA hB hC p hp).ambientMap x =
      (chartSystem f g).chart p x :=
  chart_rangeRestriction f g (range_subset_goodPairContainer f g p hp) x

theorem goodPairLocalDomain_locus (p : PairIndex f g) (hp : p ∈ goodPairs f g) :
    (goodPairLocalDomain f g hA hB hC p hp).locus = range ((chartSystem f g).chart p) :=
  (goodPairLocalDomain f g hA hB hC p hp).range_ambientMap.symm.trans
    (congrArg range (funext (goodPairLocalDomain_ambientMap f g hA hB hC p hp)))

/-- The literal raw pair image is now an original index of the actual
full local-domain saturation, with no nonempty-image requirement. -/
def goodPairSaturatedIndex (p : PairIndex f g) (hp : p ∈ goodPairs f g) :
    (localAtlas f g hA hB hC).saturatedAtlas.Index :=
  ⟨(goodPairLocalDomain f g hA hB hC p hp).locus, ⟨_, rfl⟩⟩

theorem range_goodPairSaturatedIndex (p : PairIndex f g) (hp : p ∈ goodPairs f g) :
    range ((localAtlas f g hA hB hC).saturatedAtlas.chart
      (goodPairSaturatedIndex f g hA hB hC p hp)) =
        range ((chartSystem f g).chart p) :=
  ((localAtlas f g hA hB hC).range_saturatedChart _).trans
    (goodPairLocalDomain_locus f g hA hB hC p hp)

/-- Actual full-domain uniqueness compares the unchanged original pair
algebra with the chosen saturated representative by complete bounded maps. -/
def goodPairSaturatedEquiv (p : PairIndex f g) (hp : p ∈ goodPairs f g) :
    BoundedAlgEquiv K (algebra f g p)
      ((localAtlas f g hA hB hC).saturatedAtlas.algebra
        (goodPairSaturatedIndex f g hA hB hC p hp)) :=
  (localAtlas f g hA hB hC).localDomainSaturatedEquiv
    (goodPairLocalDomain f g hA hB hC p hp)

theorem goodPairSaturatedEquiv_chart (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (x : BanachSpectrum
      ((localAtlas f g hA hB hC).saturatedAtlas.algebra
        (goodPairSaturatedIndex f g hA hB hC p hp))) :
    (chartSystem f g).chart p ((goodPairSaturatedEquiv f g hA hB hC p hp).spectrumHomeomorph x) =
      (localAtlas f g hA hB hC).saturatedAtlas.chart
        (goodPairSaturatedIndex f g hA hB hC p hp) x := by
  let a := localAtlas f g hA hB hC
  let U := goodPairLocalDomain f g hA hB hC p hp
  let S := goodPairSaturatedIndex f g hA hB hC p hp
  let e := LocalDomain.isoOfLocusEq U (a.saturatedRepresentative S)
    (a.saturatedRepresentative_locus S).symm
  exact (goodPairLocalDomain_ambientMap f g hA hB hC p hp
    ((goodPairSaturatedEquiv f g hA hB hC p hp).spectrumHomeomorph x)).symm.trans
      (e.inv.ambientMap_naturality x)

/-- Reexpression over every containing original product chart retains
the complete original raw range restriction. In the empty case, finite
full-domain separation proves that the target algebra is the zero ring. -/
theorem goodPairLocalDomain_chartRestriction (p : PairIndex f g) (hp : p ∈ goodPairs f g)
    (j : LocalAtlasIndex f g)
    (h : (goodPairLocalDomain f g hA hB hC p hp).locus ⊆
      range ((localAtlas f g hA hB hC).chart j)) :
    (localAtlas f g hA hB hC).domainChartRestriction
      (goodPairLocalDomain f g hA hB hC p hp).index j
      (goodPairLocalDomain f g hA hB hC p hp).domain h =
        rangeRestriction f g
          ((goodPairLocalDomain_locus f g hA hB hC p hp).symm.subset.trans h) := by
  classical
  by_cases hne : (range ((chartSystem f g).chart p)).Nonempty
  · have hsub : range ((chartSystem f g).chart (goodPairContainer f g p hp).rep) ⊆
        range ((chartSystem f g).chart j.rep) :=
      (range_goodPairContainer_of_nonempty f g p hp hne).subset.trans
        ((goodPairLocalDomain_locus f g hA hB hC p hp).symm.subset.trans h)
    exact ((localAtlas f g hA hB hC).domainChartRestriction_of_chartSubset
      (goodPairContainer f g p hp) j
      (rangeDomain f g (range_subset_goodPairContainer f g p hp)) h hsub).trans
        (rangeRestriction_comp f g (range_subset_goodPairContainer f g p hp) hsub).symm
  · have he : IsEmpty (BanachSpectrum (algebra f g p)) :=
      ⟨fun x => hne ⟨(chartSystem f g).chart p x, x, rfl⟩⟩
    exact BoundedAlgHom.ext fun _ =>
      @Subsingleton.elim (algebra f g p)
        (PresentedAffinoidAlgebra.subsingleton_of_isEmpty he) _ _

/-- Original raw restrictions are actual arrows of local full domains;
the equations over every containing original chart are whole-map equations. -/
def goodPairLocalDomainInclusion {p q : PairIndex f g}
    (hp : p ∈ goodPairs f g) (hq : q ∈ goodPairs f g)
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    goodPairLocalDomain f g hA hB hC p hp ⟶ goodPairLocalDomain f g hA hB hC q hq where
  subset := (goodPairLocalDomain_locus f g hA hB hC p hp).subset.trans
    (h.trans (goodPairLocalDomain_locus f g hA hB hC q hq).symm.subset)
  restriction := rangeRestriction f g h
  comp_chart j hU hV :=
    (congrArg (fun φ : BoundedAlgHom K
      ((localAtlas f g hA hB hC).algebra j) (algebra f g q) =>
        (rangeRestriction f g h).comp φ)
      (goodPairLocalDomain_chartRestriction f g hA hB hC q hq j hV)).trans
        ((rangeRestriction_comp f g h
          ((goodPairLocalDomain_locus f g hA hB hC q hq).symm.subset.trans hV)).symm.trans
            (goodPairLocalDomain_chartRestriction f g hA hB hC p hp j hU).symm)

theorem goodPairSaturatedIndex_subset {p q : PairIndex f g}
    (hp : p ∈ goodPairs f g) (hq : q ∈ goodPairs f g)
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    range ((localAtlas f g hA hB hC).saturatedAtlas.chart
      (goodPairSaturatedIndex f g hA hB hC p hp)) ⊆
        range ((localAtlas f g hA hB hC).saturatedAtlas.chart
          (goodPairSaturatedIndex f g hA hB hC q hq)) :=
  (range_goodPairSaturatedIndex f g hA hB hC p hp).subset.trans
    (h.trans (range_goodPairSaturatedIndex f g hA hB hC q hq).symm.subset)

/-- The bounded comparisons are natural on every entire raw range
restriction, including restrictions to empty overlaps. -/
theorem goodPairSaturatedEquiv_naturality {p q : PairIndex f g}
    (hp : p ∈ goodPairs f g) (hq : q ∈ goodPairs f g)
    (h : range ((chartSystem f g).chart p) ⊆ range ((chartSystem f g).chart q)) :
    ((localAtlas f g hA hB hC).saturatedAtlas.restriction
      (goodPairSaturatedIndex f g hA hB hC p hp)
      (goodPairSaturatedIndex f g hA hB hC q hq)
      (goodPairSaturatedIndex_subset f g hA hB hC hp hq h)).comp
        (goodPairSaturatedEquiv f g hA hB hC q hq).toBoundedAlgHom =
      (goodPairSaturatedEquiv f g hA hB hC p hp).toBoundedAlgHom.comp
        (rangeRestriction f g h) := by
  let a := localAtlas f g hA hB hC
  let U := goodPairLocalDomain f g hA hB hC p hp
  let V := goodPairLocalDomain f g hA hB hC q hq
  let S := goodPairSaturatedIndex f g hA hB hC p hp
  let T := goodPairSaturatedIndex f g hA hB hC q hq
  let e := LocalDomain.isoOfLocusEq U (a.saturatedRepresentative S)
    (a.saturatedRepresentative_locus S).symm
  let e' := LocalDomain.isoOfLocusEq V (a.saturatedRepresentative T)
    (a.saturatedRepresentative_locus T).symm
  let r := goodPairLocalDomainInclusion f g hA hB hC hp hq h
  let s := a.saturatedInclusion S T (goodPairSaturatedIndex_subset f g hA hB hC hp hq h)
  have he : s ≫ e'.inv = e.inv ≫ r :=
    @Subsingleton.elim (LocalDomain.Inclusion (a.saturatedRepresentative S) V) inferInstance _ _
  exact congrArg LocalDomain.Inclusion.restriction he

end Langlands.Analytic.FibreProduct
