import Langlands.Geometry.Analytic.FibreProductPatchTopology

/-! # Hausdorffness of local fibre-product patches -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FibreProduct

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : CompatibleStrongHom A C) (g : CompatibleStrongHom B C)

private theorem isCompact_inter_in_subspace {X : Type*} [TopologicalSpace X]
    {S T W : Set X} [T2Space W] (hS : IsCompact S) (hT : IsCompact T)
    (hSW : S ⊆ W) (hTW : T ⊆ W) : IsCompact (S ∩ T) := by
  have hS' : IsCompact (Subtype.val ⁻¹' S : Set W) :=
    IsInducing.subtypeVal.isCompact_preimage' hS (by simpa only [Subtype.range_coe] using hSW)
  have hT' : IsCompact (Subtype.val ⁻¹' T : Set W) :=
    IsInducing.subtypeVal.isCompact_preimage' hT (by simpa only [Subtype.range_coe] using hTW)
  have hc := (hS'.inter hT').image continuous_subtype_val
  have heq : Subtype.val ''
      ((Subtype.val ⁻¹' S : Set W) ∩ Subtype.val ⁻¹' T) = S ∩ T := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hSW hx.1⟩, hx, rfl⟩
  rwa [heq] at hc

/-- A finite pair-chart cover only needs the compact factor images to lie
in one open Hausdorff base patch. The original chosen base charts need not
be contained in this patch. -/
theorem exists_finite_pairs_in_open_base
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) {W : Set C.space} (hW : IsOpen W) [T2Space W]
    (a : A.atlas.Index) (b : B.atlas.Index)
    (haW : f.baseMap '' range (A.atlas.chart a) ⊆ W)
    (hbW : g.baseMap '' range (B.atlas.chart b) ⊆ W) :
    ∃ Q : Set (PairIndex f g), Q.Finite ∧
      (∀ q ∈ Q, range (A.atlas.chart q.val.1) ⊆ range (A.atlas.chart a) ∧
        range (B.atlas.chart q.val.2) ⊆ range (B.atlas.chart b)) ∧
      fst f g ⁻¹' range (A.atlas.chart a) ∩ snd f g ⁻¹' range (B.atlas.chart b) =
        ⋃ q ∈ Q, range ((chartSystem f g).chart q) := by
  classical
  obtain ⟨k, hk⟩ := f.target_exists a
  obtain ⟨l, hl⟩ := g.target_exists b
  have hcompact : IsCompact
      (f.baseMap '' range (A.atlas.chart a) ∩ g.baseMap '' range (B.atlas.chart b)) :=
    isCompact_inter_in_subspace
      ((isCompact_range (A.atlas.isEmbedding_chart a).continuous).image f.baseMap.continuous)
      ((isCompact_range (B.atlas.isEmbedding_chart b).continuous).image g.baseMap.continuous)
      haW hbW
  obtain ⟨S, hS, hSsub, hScov⟩ := C.atlas.exists_finite_charts_cover_inter_open hC hW
    hcompact k l (fun _ hx => ⟨⟨hk hx.1, hl hx.2⟩, haW hx.1⟩)
  have hc : ∀ m : S, ∃ c : A.atlas.Index, range (A.atlas.chart c) =
      range (A.atlas.chart a) ∩ f.baseMap ⁻¹' range (C.atlas.chart m.1) := fun m =>
    exists_chart_preimage hA a hk
      ((hSsub m.1 m.2).trans (inter_subset_left.trans inter_subset_left))
  have hd : ∀ m : S, ∃ d : B.atlas.Index, range (B.atlas.chart d) =
      range (B.atlas.chart b) ∩ g.baseMap ⁻¹' range (C.atlas.chart m.1) := fun m =>
    exists_chart_preimage hB b hl
      ((hSsub m.1 m.2).trans (inter_subset_left.trans inter_subset_right))
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
      have hs : f.baseMap (fst f g z) ∈
          f.baseMap '' range (A.atlas.chart a) ∩ g.baseMap '' range (B.atlas.chart b) :=
        ⟨⟨_, hx, rfl⟩, ⟨_, hy, (baseMap_fst f g z).symm⟩⟩
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

/-- The first projection of a patch point belongs to its factor patch. -/
theorem fst_patchMap_mem (U : Set A.space) (V : Set B.space)
    (z : (patchSystem f g U V).Space) : fst f g (patchMap f g U V z) ∈ U := by
  obtain ⟨p, t, rfl⟩ := (patchSystem f g U V).exists_chart z
  exact p.property.1 ⟨_, rfl⟩

/-- The second projection of a patch point belongs to its factor patch. -/
theorem snd_patchMap_mem (U : Set A.space) (V : Set B.space)
    (z : (patchSystem f g U V).Space) : snd f g (patchMap f g U V z) ∈ V := by
  obtain ⟨p, t, rfl⟩ := (patchSystem f g U V).exists_chart z
  exact p.property.2 ⟨_, rfl⟩

/-- The first projection to the actual factor subspace. -/
def patchFst (U : Set A.space) (V : Set B.space)
    (z : (patchSystem f g U V).Space) : U :=
  ⟨fst f g (patchMap f g U V z), fst_patchMap_mem f g U V z⟩

/-- The second projection to the actual factor subspace. -/
def patchSnd (U : Set A.space) (V : Set B.space)
    (z : (patchSystem f g U V).Space) : V :=
  ⟨snd f g (patchMap f g U V z), snd_patchMap_mem f g U V z⟩

theorem continuous_patchFst (U : Set A.space) (V : Set B.space) :
    Continuous (patchFst f g U V) :=
  ((continuous_fst f g).comp ((chartSystem f g).continuous_subsystemMap
    (patchPairs f g U V) (isDownwardClosed_patchPairs f g U V))).subtype_mk _

theorem continuous_patchSnd (U : Set A.space) (V : Set B.space) :
    Continuous (patchSnd f g U V) :=
  ((continuous_snd f g).comp ((chartSystem f g).continuous_subsystemMap
    (patchPairs f g U V) (isDownwardClosed_patchPairs f g U V))).subtype_mk _

/-- The exact pair-chart image formula also holds in the patch quotient. -/
theorem mem_range_patchChart_iff (U : Set A.space) (V : Set B.space)
    (p : (patchSystem f g U V).Index) (z : (patchSystem f g U V).Space) :
    z ∈ range ((patchSystem f g U V).chart p) ↔
      (patchFst f g U V z).val ∈ range (A.atlas.chart p.val.val.1) ∧
      (patchSnd f g U V z).val ∈ range (B.atlas.chart p.val.val.2) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨_, rfl⟩, ⟨_, rfl⟩⟩
  · intro hz
    obtain ⟨t, ht⟩ := (mem_range_chart_iff f g p.val (patchMap f g U V z)).mpr hz
    exact ⟨t, (chartSystem f g).subsystemMap_injective (patchPairs f g U V)
      (isDownwardClosed_patchPairs f g U V) ht⟩

/-- The patch chart is the intersection of the two factor-chart preimages. -/
theorem range_patchChart (U : Set A.space) (V : Set B.space)
    (p : (patchSystem f g U V).Index) :
    range ((patchSystem f g U V).chart p) =
      patchFst f g U V ⁻¹' range (A.atlas.subspaceChart U ⟨p.val.val.1, p.property.1⟩) ∩
      patchSnd f g U V ⁻¹' range (B.atlas.subspaceChart V ⟨p.val.val.2, p.property.2⟩) := by
  ext z
  constructor
  · intro hz
    obtain ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ := (mem_range_patchChart_iff f g U V p z).mp hz
    exact ⟨⟨s, Subtype.ext hs⟩, ⟨t, Subtype.ext ht⟩⟩
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    exact (mem_range_patchChart_iff f g U V p z).mpr
      ⟨⟨s, congrArg Subtype.val hs⟩, ⟨t, congrArg Subtype.val ht⟩⟩

/-- Finite pair-chart covers in the actual restricted quotient. -/
theorem exists_finite_patchPairs (U : Set A.space) (V : Set B.space)
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) {W : Set C.space} (hW : IsOpen W) [T2Space W]
    (hUW : f.baseMap '' U ⊆ W) (hVW : g.baseMap '' V ⊆ W)
    (a : A.atlas.SubspaceChart U) (b : B.atlas.SubspaceChart V) :
    ∃ R : Set (patchSystem f g U V).Index, R.Finite ∧
      patchFst f g U V ⁻¹' range (A.atlas.subspaceChart U a) ∩
        patchSnd f g U V ⁻¹' range (B.atlas.subspaceChart V b) =
          ⋃ q ∈ R, range ((patchSystem f g U V).chart q) := by
  classical
  obtain ⟨Q, hQ, hQsub, hQeq⟩ := exists_finite_pairs_in_open_base f g hA hB hC hW
    a.val b.val ((image_mono a.property).trans hUW) ((image_mono b.property).trans hVW)
  let q : Q → (patchSystem f g U V).Index := fun p =>
    ⟨p.val, (hQsub p.val p.property).1.trans a.property,
      (hQsub p.val p.property).2.trans b.property⟩
  let : Fintype Q := hQ.fintype
  refine ⟨range q, finite_range q, ?_⟩
  ext z
  simp only [mem_inter_iff, mem_preimage, mem_iUnion, exists_prop]
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩
    have hz : patchMap f g U V z ∈
        fst f g ⁻¹' range (A.atlas.chart a.val) ∩
          snd f g ⁻¹' range (B.atlas.chart b.val) :=
      ⟨⟨s, congrArg Subtype.val hs⟩, ⟨t, congrArg Subtype.val ht⟩⟩
    rw [hQeq] at hz
    obtain ⟨p, hp, hzp⟩ := mem_iUnion₂.mp hz
    refine ⟨q ⟨p, hp⟩, ⟨⟨p, hp⟩, rfl⟩, ?_⟩
    exact (mem_range_patchChart_iff f g U V (q ⟨p, hp⟩) z).mpr
      ((mem_range_chart_iff f g p _).mp hzp)
  · rintro ⟨_, ⟨p, rfl⟩, hz⟩
    have hpz := (mem_range_patchChart_iff f g U V (q p) z).mp hz
    obtain ⟨s, hs⟩ := (hQsub p.val p.property).1 hpz.1
    obtain ⟨t, ht⟩ := (hQsub p.val p.property).2 hpz.2
    exact ⟨⟨s, Subtype.ext hs⟩, ⟨t, Subtype.ext ht⟩⟩

/-- The nonempty original pair-chart ranges in the patch quotient. -/
def patchChartFamily (U : Set A.space) (V : Set B.space) :
    Set (Set (patchSystem f g U V).Space) :=
  {T | T.Nonempty ∧ ∃ p, range ((patchSystem f g U V).chart p) = T}

theorem patchChartFamily_subset (U : Set A.space) (V : Set B.space) :
    patchChartFamily f g U V ⊆
      AtlasTopology.preimageProductFamily (patchFst f g U V) (patchSnd f g U V)
        (range fun a => range (A.atlas.subspaceChart U a))
        (range fun b => range (B.atlas.subspaceChart V b)) := by
  rintro _ ⟨hne, p, rfl⟩
  exact ⟨hne, _, ⟨⟨p.val.val.1, p.property.1⟩, rfl⟩,
    _, ⟨⟨p.val.val.2, p.property.2⟩, rfl⟩, range_patchChart f g U V p⟩

/-- Finite closed pair-chart covers give the relative local refinement. -/
theorem locallyRefines_patchChartFamily (U : Set A.space) (V : Set B.space)
    [T2Space U] [T2Space V]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) {W : Set C.space} (hW : IsOpen W) [T2Space W]
    (hUW : f.baseMap '' U ⊆ W) (hVW : g.baseMap '' V ⊆ W) :
    AtlasTopology.LocallyRefines (patchChartFamily f g U V)
      (AtlasTopology.preimageProductFamily (patchFst f g U V) (patchSnd f g U V)
        (range fun a => range (A.atlas.subspaceChart U a))
        (range fun b => range (B.atlas.subspaceChart V b))) := by
  classical
  rintro _ ⟨-, _, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩ z hz
  obtain ⟨R, hR, hReq⟩ := exists_finite_patchPairs f g U V hA hB hC hW hUW hVW a b
  let P := patchSystem f g U V
  let σ : Set (Set P.Space) :=
    (fun q => range (P.chart q)) '' {q | q ∈ R ∧ z ∈ range (P.chart q)}
  let F : Set P.Space :=
    ⋃ q ∈ {q | q ∈ R ∧ z ∉ range (P.chart q)}, range (P.chart q)
  have hF : IsClosed F :=
    (hR.subset fun q hq => hq.1).isClosed_biUnion fun q _ =>
      (isClosedEmbedding_patchChart f g U V q).isClosed_range
  have hzF : z ∉ F := by
    simp only [F, mem_iUnion]
    rintro ⟨q, ⟨-, hzq⟩, hz'⟩
    exact hzq hz'
  refine ⟨σ, (hR.subset fun q hq => hq.1).image _, ?_, ?_, ?_⟩
  · rintro _ ⟨q, ⟨-, hzq⟩, rfl⟩
    exact ⟨⟨z, hzq⟩, q, rfl⟩
  · rintro _ ⟨q, ⟨hqR, hzq⟩, rfl⟩
    refine ⟨?_, hzq⟩
    rw [hReq]
    exact subset_biUnion_of_mem (u := fun q => range (P.chart q)) hqR
  · apply mem_nhdsWithin.mpr
    refine ⟨Fᶜ, hF.isOpen_compl, hzF, ?_⟩
    rintro y ⟨hyF, hyM⟩
    rw [hReq] at hyM
    obtain ⟨q, hqR, hyq⟩ := mem_iUnion₂.mp hyM
    have hzq : z ∈ range (P.chart q) := by
      by_contra hzq
      exact hyF (mem_biUnion (show q ∈ {q | q ∈ R ∧ z ∉ range (P.chart q)}
        from ⟨hqR, hzq⟩) hyq)
    exact ⟨_, ⟨q, ⟨hqR, hzq⟩, rfl⟩, hyq⟩

/-- The actual patch quotient has its net of nonempty original pair charts. -/
theorem isNet_patchChartFamily {U : Set A.space} {V : Set B.space}
    (hU : IsOpen U) (hV : IsOpen V) [T2Space U] [T2Space V]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) {W : Set C.space} (hW : IsOpen W) [T2Space W]
    (hUW : f.baseMap '' U ⊆ W) (hVW : g.baseMap '' V ⊆ W) :
    AtlasTopology.IsNet (patchChartFamily f g U V) :=
  (AtlasTopology.IsNet.preimageProductFamily
    (continuous_patchFst f g U V) (continuous_patchSnd f g U V)
    (A.atlas.isNet_subspaceChartFamily U (hA.isOriginalChartDomain_of_isOpen hU))
    (B.atlas.isNet_subspaceChartFamily V (hB.isOriginalChartDomain_of_isOpen hV))).of_locallyRefines
      (patchChartFamily_subset f g U V)
      (locallyRefines_patchChartFamily f g U V hA hB hC hW hUW hVW)

/-- A fibre-product patch over one open Hausdorff base patch is Hausdorff. -/
theorem t2Space_patchSystem {U : Set A.space} {V : Set B.space}
    (hU : IsOpen U) (hV : IsOpen V) [T2Space U] [T2Space V]
    (hA : A.atlas.HasAllLocalDomains) (hB : B.atlas.HasAllLocalDomains)
    (hC : C.atlas.HasAllLocalDomains) {W : Set C.space} (hW : IsOpen W) [T2Space W]
    (hUW : f.baseMap '' U ⊆ W) (hVW : g.baseMap '' V ⊆ W) :
    T2Space (patchSystem f g U V).Space := by
  refine ((isNet_patchChartFamily f g hU hV hA hB hC hW hUW hVW).1.t2Space_iff ?_).mpr ?_
  · rintro _ ⟨-, p, rfl⟩
    refine ⟨isCompact_range ((patchSystem f g U V).continuous_chart p), ?_⟩
    exact (isClosedEmbedding_patchChart f g U V p).isEmbedding.toHomeomorph.t2Space
  · rintro _ ⟨-, p, rfl⟩ _ ⟨-, q, rfl⟩
    exact (isCompact_range ((patchSystem f g U V).continuous_chart p)).inter_right
      (isClosedEmbedding_patchChart f g U V q).isClosed_range

end Langlands.Analytic.FibreProduct
