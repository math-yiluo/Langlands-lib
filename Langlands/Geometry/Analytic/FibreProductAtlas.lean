import Langlands.Geometry.Analytic.FibreProductRestriction
import Langlands.Geometry.Analytic.AffinoidProductAtlas
import Langlands.Geometry.Analytic.SaturatedAtlasDomainClosure

/-! # The affinoid atlas of a fibre product of analytic spaces -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace FibreProduct

open AffinoidAtlasPresentation

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

/-! ## Preimages of base charts in saturated atlases -/

variable {f} in
/-- In an atlas containing all local domains, the preimage in a chart `V` of a base chart
`W'` contained in a base chart `W ⊇ f(V)` is a chart. -/
theorem exists_chart_preimage (hA : A.atlas.HasAllLocalDomains) (a : A.atlas.Index)
    {k m : C.atlas.Index} (hk : f.baseMap '' range (A.atlas.chart a) ⊆ range (C.atlas.chart k))
    (hmk : range (C.atlas.chart m) ⊆ range (C.atlas.chart k)) :
    ∃ c : A.atlas.Index,
      range (A.atlas.chart c) = range (A.atlas.chart a) ∩ f.baseMap ⁻¹' range (C.atlas.chart m) := by
  let U : IndexedAffinoidAtlas.LocalDomain A.atlas :=
    ⟨a, Domain.pullback (f.pullback a k hk) (C.atlas.restrictionDomain m k hmk)⟩
  obtain ⟨c, hc⟩ := hA.exists_chart U
  refine ⟨c, hc.trans ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, ?_⟩
    change C.atlas.chart k (BanachSpectrum.comap (f.pullback a k hk).toBoundedRingHom x) ∈
      range (C.atlas.chart m) at hx
    rw [f.chart_comm] at hx
    exact hx
  · rintro ⟨⟨x, rfl⟩, hx⟩
    refine ⟨x, ?_, rfl⟩
    change C.atlas.chart k (BanachSpectrum.comap (f.pullback a k hk).toBoundedRingHom x) ∈
      range (C.atlas.chart m)
    rw [f.chart_comm]
    exact hx

/-- Over a Hausdorff base and atlases containing all local domains, the preimage of two
factor charts in the glued fibre product is a finite union of pair charts, each of whose
factor charts lies in the given ones. -/
theorem exists_finite_pairs [T2Space C.space] (hA : A.atlas.HasAllLocalDomains)
    (hB : B.atlas.HasAllLocalDomains) (a : A.atlas.Index) (b : B.atlas.Index) :
    ∃ Q : Set (PairIndex f g), Q.Finite ∧
      (∀ q ∈ Q, range (A.atlas.chart q.1.1) ⊆ range (A.atlas.chart a) ∧
        range (B.atlas.chart q.1.2) ⊆ range (B.atlas.chart b)) ∧
      fst f g ⁻¹' range (A.atlas.chart a) ∩ snd f g ⁻¹' range (B.atlas.chart b) =
        ⋃ q ∈ Q, range ((chartSystem f g).chart q) := by
  classical
  obtain ⟨k, hk⟩ := f.target_exists a
  obtain ⟨l, hl⟩ := g.target_exists b
  obtain ⟨S, hS, hSsub, hScov⟩ :=
    IndexedAffinoidAtlas.exists_finite_charts_inter (a := C.atlas) k l
  have hc : ∀ m : S, ∃ c : A.atlas.Index, range (A.atlas.chart c) =
      range (A.atlas.chart a) ∩ f.baseMap ⁻¹' range (C.atlas.chart m.1) := fun m =>
    exists_chart_preimage hA a hk ((hSsub m.1 m.2).trans inter_subset_left)
  have hd : ∀ m : S, ∃ d : B.atlas.Index, range (B.atlas.chart d) =
      range (B.atlas.chart b) ∩ g.baseMap ⁻¹' range (C.atlas.chart m.1) := fun m =>
    exists_chart_preimage hB b hl ((hSsub m.1 m.2).trans inter_subset_right)
  choose c hc using hc
  choose d hd using hd
  let q : S → PairIndex f g := fun m => ⟨(c m, d m), m.1,
    ⟨by
      rintro _ ⟨y, hy, rfl⟩
      rw [hc m] at hy
      exact hy.2,
    by
      rintro _ ⟨y, hy, rfl⟩
      rw [hd m] at hy
      exact hy.2⟩⟩
  have hSf : Finite S := hS.to_subtype
  refine ⟨range q, finite_range q, ?_, ?_⟩
  · rintro _ ⟨m, rfl⟩
    exact ⟨(hc m).symm ▸ inter_subset_left, (hd m).symm ▸ inter_subset_left⟩
  · ext z
    simp only [mem_inter_iff, mem_preimage, mem_iUnion, exists_prop]
    constructor
    · rintro ⟨hx, hy⟩
      have hs : f.baseMap (fst f g z) ∈ range (C.atlas.chart k) ∩ range (C.atlas.chart l) :=
        ⟨hk ⟨_, hx, rfl⟩, (baseMap_fst f g z).symm ▸ hl ⟨_, hy, rfl⟩⟩
      obtain ⟨m, hmS, hm⟩ := mem_iUnion₂.1 (hScov hs)
      refine ⟨q ⟨m, hmS⟩, ⟨⟨m, hmS⟩, rfl⟩, ?_⟩
      rw [mem_range_chart_iff]
      refine ⟨?_, ?_⟩
      · change fst f g z ∈ range (A.atlas.chart (c ⟨m, hmS⟩))
        rw [hc]
        exact ⟨hx, hm⟩
      · change snd f g z ∈ range (B.atlas.chart (d ⟨m, hmS⟩))
        rw [hd]
        refine ⟨hy, ?_⟩
        show g.baseMap (snd f g z) ∈ range (C.atlas.chart m)
        rw [← baseMap_fst]
        exact hm
    · rintro ⟨_, ⟨m, rfl⟩, hz⟩
      rw [mem_range_chart_iff] at hz
      obtain ⟨hx, hy⟩ := hz
      change fst f g z ∈ range (A.atlas.chart (c m)) at hx
      change snd f g z ∈ range (B.atlas.chart (d m)) at hy
      rw [hc] at hx
      rw [hd] at hy
      exact ⟨hx.1, hy.1⟩

/-! ## The chart family -/

/-- The nonempty chart ranges of the glued fibre product. -/
def chartFamily : Set (Set (chartSystem f g).Space) :=
  {T | T.Nonempty ∧ ∃ p, range ((chartSystem f g).chart p) = T}

theorem chartFamily_subset :
    chartFamily f g ⊆ AtlasTopology.preimageProductFamily (fst f g) (snd f g)
      (range fun i => range (A.atlas.chart i)) (range fun j => range (B.atlas.chart j)) := by
  rintro _ ⟨hne, p, rfl⟩
  exact ⟨hne, _, ⟨p.1.1, rfl⟩, _, ⟨p.1.2, rfl⟩, range_chart f g p⟩

theorem isClosed_range_chart [T2Space A.space] [T2Space B.space] (p : PairIndex f g) :
    IsClosed (range ((chartSystem f g).chart p)) :=
  (isClosedEmbedding_chart f g p).isClosed_range

theorem locallyRefines_chartFamily [T2Space A.space] [T2Space B.space] [T2Space C.space]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains) :
    AtlasTopology.LocallyRefines (chartFamily f g)
      (AtlasTopology.preimageProductFamily (fst f g) (snd f g)
        (range fun i => range (A.atlas.chart i)) (range fun j => range (B.atlas.chart j))) := by
  classical
  rintro _ ⟨-, _, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ z hz
  obtain ⟨Q, hQ, hQsub, hQeq⟩ := exists_finite_pairs f g hA hB a b
  let σ : Set (Set (chartSystem f g).Space) :=
    (fun q => range ((chartSystem f g).chart q)) '' {q | q ∈ Q ∧ z ∈ range ((chartSystem f g).chart q)}
  let F : Set (chartSystem f g).Space :=
    ⋃ q ∈ {q | q ∈ Q ∧ z ∉ range ((chartSystem f g).chart q)}, range ((chartSystem f g).chart q)
  have hF : IsClosed F :=
    (hQ.subset fun q hq => hq.1).isClosed_biUnion fun q _ => isClosed_range_chart f g q
  have hzF : z ∉ F := by
    simp only [F, mem_iUnion]
    rintro ⟨q, ⟨-, hzq⟩, hz'⟩
    exact hzq hz'
  refine ⟨σ, (hQ.subset fun q hq => hq.1).image _, ?_, ?_, ?_⟩
  · rintro _ ⟨q, ⟨-, hzq⟩, rfl⟩
    exact ⟨⟨z, hzq⟩, q, rfl⟩
  · rintro _ ⟨q, ⟨hqQ, hzq⟩, rfl⟩
    refine ⟨?_, hzq⟩
    rw [hQeq]
    exact subset_biUnion_of_mem (u := fun q => range ((chartSystem f g).chart q)) hqQ
  · apply mem_nhdsWithin.2
    refine ⟨Fᶜ, hF.isOpen_compl, hzF, ?_⟩
    rintro w ⟨hwF, hwM⟩
    rw [hQeq] at hwM
    obtain ⟨q, hqQ, hwq⟩ := mem_iUnion₂.1 hwM
    have hzq : z ∈ range ((chartSystem f g).chart q) := by
      by_contra hzq
      exact hwF (mem_biUnion (show q ∈ {q | q ∈ Q ∧ z ∉ range ((chartSystem f g).chart q)}
        from ⟨hqQ, hzq⟩) hwq)
    exact ⟨_, ⟨q, ⟨hqQ, hzq⟩, rfl⟩, hwq⟩

theorem isNet_chartFamily [T2Space A.space] [T2Space B.space] [T2Space C.space]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains) :
    AtlasTopology.IsNet (chartFamily f g) :=
  (AtlasTopology.IsNet.preimageProductFamily (continuous_fst f g) (continuous_snd f g)
    A.atlas.isNet_chartFamily B.atlas.isNet_chartFamily).of_locallyRefines
      (chartFamily_subset f g) (locallyRefines_chartFamily f g hA hB)

/-- The glued fibre product of Hausdorff spaces is Hausdorff. -/
theorem t2Space [T2Space A.space] [T2Space B.space] [T2Space C.space]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains) :
    T2Space (chartSystem f g).Space := by
  refine ((isNet_chartFamily f g hA hB).1.t2Space_iff ?_).2 ?_
  · rintro _ ⟨-, p, rfl⟩
    refine ⟨isCompact_range ((chartSystem f g).continuous_chart p), ?_⟩
    exact (isClosedEmbedding_chart f g p).isEmbedding.toHomeomorph.t2Space
  · rintro _ ⟨-, p, rfl⟩ _ ⟨-, q, rfl⟩
    exact (isCompact_range ((chartSystem f g).continuous_chart p)).inter_right
      (isClosed_range_chart f g q)

/-! ## The atlas -/

/-- The indices of the fibre product atlas: the nonempty chart ranges. -/
def AtlasIndex : Type (max u w) := {T : Set (chartSystem f g).Space // T ∈ chartFamily f g}

variable {f g} in
/-- A chosen pair whose chart has the given range. -/
def AtlasIndex.rep (T : AtlasIndex f g) : PairIndex f g := T.2.2.choose

variable {f g} in
theorem AtlasIndex.range_rep (T : AtlasIndex f g) :
    range ((chartSystem f g).chart T.rep) = T.1 :=
  T.2.2.choose_spec

theorem range_rep_eq_chartFamily :
    range (fun T : AtlasIndex f g => range ((chartSystem f g).chart T.rep)) = chartFamily f g := by
  ext S
  constructor
  · rintro ⟨T, rfl⟩
    show range ((chartSystem f g).chart T.rep) ∈ chartFamily f g
    rw [T.range_rep]
    exact T.2
  · intro hS
    exact ⟨⟨S, hS⟩, AtlasIndex.range_rep ⟨S, hS⟩⟩

variable [T2Space A.space] [T2Space B.space] [T2Space C.space]
  (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)

/-- The affinoid atlas of the fibre product `X ×_S Y`: its charts are the nonempty charts
`V ×_W U` of the glued space, with the restrictions between charts with included ranges. -/
def atlas : IndexedAffinoidAtlas.{u, max u w, max u w} K (chartSystem f g).Space where
  Index := AtlasIndex f g
  algebra T := algebra f g T.rep
  chart T := (chartSystem f g).chart T.rep
  isEmbedding_chart T := (isClosedEmbedding_chart f g T.rep).isEmbedding
  chartDomain_injective T T' h :=
    Subtype.ext ((AtlasIndex.range_rep T).symm.trans (h.trans (AtlasIndex.range_rep T')))
  locallyHausdorff _ := by
    have := t2Space f g hA hB
    exact ⟨univ, Filter.univ_mem, inferInstance⟩
  isNet_chartFamily := by
    rw [range_rep_eq_chartFamily]
    exact isNet_chartFamily f g hA hB
  restriction _ _ h := rangeRestriction f g h
  restriction_chart _ _ h x := chart_rangeRestriction f g h x
  restriction_universal _ _ h R φ hφ := rangeRestriction_universal f g h R φ hφ
  restriction_id T _ := rangeRestriction_self f g T.rep
  restriction_comp _ _ _ h₁ h₂ _ := rangeRestriction_comp f g h₁ h₂

/-- The fibre product `X ×_S Y` as an affinoid atlas presentation. -/
def presentation : AffinoidAtlasPresentation.{u, max u w, max u w} K where
  space := TopCat.of (chartSystem f g).Space
  atlas := atlas f g hA hB

end FibreProduct

end Langlands.Analytic
