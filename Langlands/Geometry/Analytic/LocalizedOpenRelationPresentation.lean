import Langlands.Geometry.Analytic.SchemeAnalytificationAtlas
import Langlands.Geometry.Analytic.LocalizedOpenRelationAtlas

/-! # The glued analytic space

The chart images form an affinoid atlas on the glued space, with all local domains. -/

noncomputable section

universe u

namespace Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation

open _root_.CategoryTheory Set Topology IndexedAffinoidAtlas PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable {R : LocalizedOpenRelation K}

theorem chartImage_mem (c : R.PieceChart) :
    c.image ∈ range (fun T : R.ChartImage => range (chartMap T)) :=
  ⟨⟨c.image, c, rfl⟩, range_chartMap _⟩

theorem range_chartMap_family :
    range (fun T : R.ChartImage => range (chartMap T)) = range (PieceChart.image (R := R)) := by
  ext V
  constructor
  · rintro ⟨T, rfl⟩
    show range (chartMap T) ∈ _
    rw [range_chartMap]
    exact T.2
  · rintro ⟨c, rfl⟩
    exact chartImage_mem c

theorem image_chart_mem (m : R.M) (i : (R.atl m).Index) :
    R.ι m '' range ((R.atl m).chart i) ∈ range (PieceChart.image (R := R)) :=
  ⟨⟨m, i⟩, rfl⟩

theorem isNet_chartImages :
    AtlasTopology.IsNet (range (PieceChart.image (R := R))) := by
  refine ⟨fun y => ?_, ?_⟩
  · obtain ⟨m, z, rfl⟩ := exists_ι_eq y
    obtain ⟨σ, hσf, hστ, hσy, hσn⟩ := (R.atl m).isNet_chartFamily.1 z
    refine ⟨Set.image (R.ι m) '' σ, hσf.image _, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      obtain ⟨i, rfl⟩ := hστ hV
      exact image_chart_mem m i
    · rintro _ ⟨V, hV, rfl⟩
      exact ⟨z, hσy V hV, rfl⟩
    · refine Filter.mem_of_superset ((isOpenEmbedding_ι m).isOpenMap.image_mem_nhds hσn) ?_
      rintro _ ⟨v, ⟨V, hV, hv⟩, rfl⟩
      exact ⟨_, ⟨V, hV, rfl⟩, v, hv, rfl⟩
  · rintro _ ⟨c₁, rfl⟩ _ ⟨c₂, rfl⟩
    apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr
    intro Y hY y hy
    rw [Set.mem_singleton_iff] at hY
    subst hY
    obtain ⟨z, hz, rfl⟩ := hy.1
    let m := c₁.m
    have hE : (R.atl m).IsOriginalChartDomain
        {z : (presentationOf (R.Z m)).presentation.space | R.ι m z ∈ c₁.image ∩ c₂.image} :=
      (isOriginalChartDomain_preimage_image m c₁).inter _
        (isOriginalChartDomain_preimage_image m c₂)
    obtain ⟨σ, hσf, hστ, hσw, hσn⟩ :=
      (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hE _ (Set.mem_singleton _) z hy
    refine ⟨Set.image (R.ι m) '' σ, hσf.image _, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      obtain ⟨i, rfl⟩ := hστ hV
      exact image_chart_mem m i
    · rintro _ ⟨V, hV, rfl⟩
      refine ⟨?_, ⟨z, (hσw V hV).2, rfl⟩⟩
      rintro _ ⟨v, hv, rfl⟩
      exact (hσw V hV).1 hv
    · refine Filter.mem_of_superset
        (Langlands.Analytic.SchemeAnalytification.image_mem_nhdsWithin_of_isOpenEmbedding (isOpenEmbedding_ι m) hσn) ?_
      rintro _ ⟨v, ⟨V, hV, hv⟩, rfl⟩
      exact ⟨_, ⟨V, hV, rfl⟩, v, hv, rfl⟩

theorem locallyHausdorff (y : R.Space) : ∃ U : Set R.Space, U ∈ 𝓝 y ∧ T2Space U := by
  obtain ⟨m, z, rfl⟩ := exists_ι_eq y
  obtain ⟨U, hU, hT2⟩ := (R.atl m).locallyHausdorff z
  refine ⟨R.ι m '' U, (isOpenEmbedding_ι m).isOpenMap.image_mem_nhds hU, ?_⟩
  have he : IsEmbedding (R.ι m ∘ Subtype.val : U → R.Space) :=
    (isOpenEmbedding_ι m).isEmbedding.comp IsEmbedding.subtypeVal
  have hr : range (R.ι m ∘ Subtype.val : U → R.Space) = R.ι m '' U := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨v.val, v.property, rfl⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨⟨v, hv⟩, rfl⟩
  exact (he.toHomeomorph.trans (Homeomorph.setCongr hr)).t2Space

variable (R) in
/-- The affinoid atlas of the glued space. -/
abbrev atlas : IndexedAffinoidAtlas.{u, u, u} K R.Space where
  Index := R.ChartImage
  algebra T := T.rep.alg
  chart T := chartMap T
  isEmbedding_chart T := (isOpenEmbedding_ι T.rep.m).isEmbedding.comp
    ((R.atl T.rep.m).isEmbedding_chart T.rep.i)
  chartDomain_injective S T h := Subtype.ext
    ((range_chartMap S).symm.trans (h.trans (range_chartMap T)))
  locallyHausdorff := locallyHausdorff
  isNet_chartFamily := by
    rw [range_chartMap_family]
    exact isNet_chartImages
  restriction S T h := rho S.rep T.rep (by
    rw [ChartImage.rep_image, ChartImage.rep_image, ← range_chartMap, ← range_chartMap]
    exact h)
  restriction_chart S T h x := rho_chart _ _ _ x
  restriction_universal S T h A φ hφ := rho_universal _ _ _ A φ fun x => by
    rw [ChartImage.rep_image, ← range_chartMap]
    exact hφ x
  restriction_id S h := rho_self _ _
  restriction_comp S T U hST hTU hSU := rho_comp _ _ _ _ _ _

theorem atlas_hasAllLocalDomains : (atlas R).HasAllLocalDomains := by
  refine Set.Subset.antisymm ?_ (atlas R).chartFamily_subset_localDomainFamily
  rintro _ ⟨L, rfl⟩
  let c := L.index.rep
  let L' : LocalDomain (R.atl c.m) := ⟨c.i, L.domain⟩
  obtain ⟨i', hi'⟩ := (presentationOf (R.Z c.m)).hasAllLocalDomains.exists_chart L'
  let d : R.PieceChart := ⟨c.m, i'⟩
  let T : R.ChartImage := ⟨d.image, d, rfl⟩
  refine ⟨T, (range_chartMap T).trans ?_⟩
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ L'.locus := hi' ▸ hz
    obtain ⟨x, hx, rfl⟩ := hz'
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    have hz : (R.atl c.m).chart c.i x ∈ range ((R.atl c.m).chart i') := hi'.symm ▸ ⟨x, hx, rfl⟩
    exact ⟨_, hz, rfl⟩

variable (R) in
/-- The glued space with its atlas, as a saturated presentation. -/
abbrev presentation : SaturatedAtlasPresentation.{u, u, u} K where
  presentation := ⟨TopCat.of R.Space, atlas R⟩
  hasAllLocalDomains := atlas_hasAllLocalDomains

variable (R) in
/-- The glued analytic space. -/
abbrev glued : LocalizedCategory.{u, u, u} (K := K) := localizationFunctor.obj R.presentation

end Langlands.Analytic.SaturatedAtlasPresentation.LocalizedOpenRelation
