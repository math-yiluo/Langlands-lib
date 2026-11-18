import Langlands.Geometry.Analytic.QuasiEtaleRigidity.StrongNearComposition
import Langlands.Geometry.Analytic.LocalizedCompactNeighborhoods
import Langlands.Geometry.Analytic.StrongNearDomainTransport

/-! # Local chart covers and gluing equality of strong maps along a source refinement -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section LocalCovers

variable (T : SaturatedAtlasPresentation.{u, v, w} K)

/-- A set `Z` is locally covered at `y` by finitely many charts with property `Q`: the charts
contain `y` and lie in `Z`, and their union contains `Z ∩ N` for a neighbourhood `N` of `y`. -/
def IsLocallyChartCovered (Q : T.presentation.atlas.Index → Prop)
    (Z : Set T.presentation.space) (y : T.presentation.space) : Prop :=
  ∃ σ : Set T.presentation.atlas.Index, σ.Finite ∧
    (∀ k ∈ σ, y ∈ Set.range (T.presentation.atlas.chart k) ∧
      Set.range (T.presentation.atlas.chart k) ⊆ Z ∧ Q k) ∧
    ∃ N ∈ 𝓝 y, Z ∩ N ⊆ ⋃ k ∈ σ, Set.range (T.presentation.atlas.chart k)

variable {T}

theorem IsLocallyChartCovered.of_subset_pred {Q : T.presentation.atlas.Index → Prop}
    {Z : Set T.presentation.space} {y : T.presentation.space}
    (h : T.IsLocallyChartCovered (fun _ => True) Z y)
    (hQ : ∀ k, Set.range (T.presentation.atlas.chart k) ⊆ Z → Q k) :
    T.IsLocallyChartCovered Q Z y := by
  obtain ⟨σ, hσ, hmem, N, hN, hcov⟩ := h
  exact ⟨σ, hσ, fun k hk => ⟨(hmem k hk).1, (hmem k hk).2.1, hQ k (hmem k hk).2.1⟩, N, hN, hcov⟩

/-- A set whose restricted chart family is a quasinet is locally chart covered. -/
theorem isLocallyChartCovered_of_isQuasinet {Z : Set T.presentation.space}
    (hZ : AtlasTopology.IsQuasinet (AtlasTopology.restrictedFamily
      (Set.range fun i => Set.range (T.presentation.atlas.chart i)) Z))
    {y : T.presentation.space} (hy : y ∈ Z) :
    T.IsLocallyChartCovered (fun _ => True) Z y := by
  classical
  obtain ⟨σ', hσ'fin, hσ', hyσ', hn⟩ := hZ ⟨y, hy⟩
  obtain ⟨N, hN, hNsub⟩ := (mem_nhds_subtype _ _ _).mp hn
  have key : ∀ W' ∈ σ', ∃ l : T.presentation.atlas.Index,
      Set.range (T.presentation.atlas.chart l) ⊆ Z ∧
        W' = Subtype.val ⁻¹' Set.range (T.presentation.atlas.chart l) := by
    intro W' hW'
    obtain ⟨V', ⟨l, rfl⟩, hVsub, rfl⟩ := hσ' hW'
    exact ⟨l, hVsub, rfl⟩
  choose l hlZ hlW using key
  refine ⟨{k | ∃ W' hW', l W' hW' = k}, hσ'fin.dependent_image l, ?_, N, hN, ?_⟩
  · rintro _ ⟨W', hW', rfl⟩
    refine ⟨?_, hlZ W' hW', trivial⟩
    have := hyσ' W' hW'
    rw [hlW W' hW'] at this
    exact this
  · rintro z ⟨hzZ, hzN⟩
    obtain ⟨W', hW', hzW'⟩ := hNsub (show (⟨z, hzZ⟩ : Z) ∈ Subtype.val ⁻¹' N from hzN)
    rw [hlW W' hW'] at hzW'
    exact Set.mem_biUnion ⟨W', hW', rfl⟩ hzW'

/-- A chart is locally chart covered at its points. -/
theorem isLocallyChartCovered_chart (k : T.presentation.atlas.Index)
    {y : T.presentation.space} (hy : y ∈ Set.range (T.presentation.atlas.chart k)) :
    T.IsLocallyChartCovered (fun _ => True) (Set.range (T.presentation.atlas.chart k)) y :=
  ⟨{k}, Set.finite_singleton k, fun k' hk' => by
    rw [Set.mem_singleton_iff.mp hk']
    exact ⟨hy, subset_rfl, trivial⟩, Set.univ, Filter.univ_mem, fun z hz =>
      Set.mem_biUnion (Set.mem_singleton k) hz.1⟩

/-- Neighbourhoods are locally chart covered. -/
theorem isLocallyChartCovered_of_mem_nhds {Z : Set T.presentation.space}
    {y : T.presentation.space} (hZ : Z ∈ 𝓝 y) :
    T.IsLocallyChartCovered (fun _ => True) Z y := by
  obtain ⟨I, hI, hmem, hN⟩ :=
    IndexedAffinoidAtlas.HasAllLocalDomains.exists_finite_chart_nhds_subset
      T.presentation.atlas T.hasAllLocalDomains y Z hZ
  exact ⟨I, hI, fun k hk => ⟨(hmem k hk).1, (hmem k hk).2, trivial⟩, _, hN,
    fun z hz => hz.2⟩

/-- Analytic domains are locally chart covered at their points. -/
theorem isLocallyChartCovered_analyticDomain (D : T.AnalyticDomain)
    {y : T.presentation.space} (hy : y ∈ D.carrier) :
    T.IsLocallyChartCovered (fun _ => True) D.carrier y :=
  isLocallyChartCovered_of_isQuasinet D.is_domain hy

/-- Finite covers by locally chart covered pieces. -/
theorem isLocallyChartCovered_of_cover {Q : T.presentation.atlas.Index → Prop} {ι : Type*}
    [Finite ι] {Z : Set T.presentation.space} {Zs : ι → Set T.presentation.space}
    {y : T.presentation.space} (hsub : ∀ i, Zs i ⊆ Z) {N₀ : Set T.presentation.space}
    (hN₀ : N₀ ∈ 𝓝 y) (hcov : Z ∩ N₀ ⊆ ⋃ i, Zs i)
    (h : ∀ i, T.IsLocallyChartCovered Q (Zs i) y) : T.IsLocallyChartCovered Q Z y := by
  choose σ hσfin hσ N hN hNcov using h
  refine ⟨⋃ i, σ i, Set.finite_iUnion hσfin, ?_, N₀ ∩ ⋂ i, N i,
    Filter.inter_mem hN₀ (Filter.iInter_mem.mpr hN), ?_⟩
  · intro k hk
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hk
    exact ⟨(hσ i k hi).1, (hσ i k hi).2.1.trans (hsub i), (hσ i k hi).2.2⟩
  · rintro z ⟨hzZ, hzN₀, hzN⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ⟨hzZ, hzN₀⟩)
    obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp (hNcov i ⟨hi, Set.mem_iInter.mp hzN i⟩)
    exact Set.mem_iUnion₂.mpr ⟨k, Set.mem_iUnion.mpr ⟨i, hk⟩, hzk⟩

/-- Intersections of locally chart covered sets. -/
theorem IsLocallyChartCovered.inter {Z₁ Z₂ : Set T.presentation.space}
    {y : T.presentation.space} (h₁ : T.IsLocallyChartCovered (fun _ => True) Z₁ y)
    (h₂ : T.IsLocallyChartCovered (fun _ => True) Z₂ y) :
    T.IsLocallyChartCovered (fun _ => True) (Z₁ ∩ Z₂) y := by
  obtain ⟨σ₁, hσ₁, hm₁, N₁, hN₁, hc₁⟩ := h₁
  obtain ⟨σ₂, hσ₂, hm₂, N₂, hN₂, hc₂⟩ := h₂
  have : Finite (σ₁ ×ˢ σ₂ : Set _) := (hσ₁.prod hσ₂).to_subtype
  refine isLocallyChartCovered_of_cover
    (Zs := fun p : (σ₁ ×ˢ σ₂ : Set _) => Set.range (T.presentation.atlas.chart p.1.1) ∩
      Set.range (T.presentation.atlas.chart p.1.2))
    (fun p => Set.inter_subset_inter (hm₁ _ p.2.1).2.1 (hm₂ _ p.2.2).2.1)
    (Filter.inter_mem hN₁ hN₂) ?_ fun p => ?_
  · rintro z ⟨⟨hz₁, hz₂⟩, hzN₁, hzN₂⟩
    obtain ⟨k₁, hk₁, hzk₁⟩ := Set.mem_iUnion₂.mp (hc₁ ⟨hz₁, hzN₁⟩)
    obtain ⟨k₂, hk₂, hzk₂⟩ := Set.mem_iUnion₂.mp (hc₂ ⟨hz₂, hzN₂⟩)
    exact Set.mem_iUnion.mpr ⟨⟨(k₁, k₂), hk₁, hk₂⟩, hzk₁, hzk₂⟩
  · exact isLocallyChartCovered_of_isQuasinet
      (T.presentation.atlas.isNet_chartFamily.2 _ (Set.mem_range_self _) _
        (Set.mem_range_self _))
      ⟨(hm₁ _ p.2.1).1, (hm₂ _ p.2.2).1⟩

variable {B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Inside a chart mapped into a target chart `m`, the preimage of another target chart is
locally chart covered. -/
theorem isLocallyChartCovered_chart_inter_preimage (c : T ⟶ B)
    (k : T.presentation.atlas.Index) (m : B.presentation.atlas.Index)
    (hkm : c.baseMap '' Set.range (T.presentation.atlas.chart k) ⊆
      Set.range (B.presentation.atlas.chart m))
    (j : B.presentation.atlas.Index) {y : T.presentation.space}
    (hy : y ∈ Set.range (T.presentation.atlas.chart k))
    (hyj : c.baseMap y ∈ Set.range (B.presentation.atlas.chart j)) :
    T.IsLocallyChartCovered (fun _ => True)
      (Set.range (T.presentation.atlas.chart k) ∩
        c.baseMap ⁻¹' Set.range (B.presentation.atlas.chart j)) y := by
  classical
  have hym : c.baseMap y ∈ Set.range (B.presentation.atlas.chart m) := hkm ⟨y, hy, rfl⟩
  obtain ⟨τ, hτ, hmem, N, hN, hcov⟩ := isLocallyChartCovered_of_isQuasinet
    (B.presentation.atlas.isNet_chartFamily.2 _ (Set.mem_range_self j) _
      (Set.mem_range_self m)) ⟨hyj, hym⟩
  have key : ∀ l ∈ τ, ∃ q : T.presentation.atlas.Index,
      Set.range (T.presentation.atlas.chart q) = Set.range (T.presentation.atlas.chart k) ∩
        c.baseMap ⁻¹' Set.range (B.presentation.atlas.chart l) := fun l hl =>
    AffinoidAtlasPresentation.StrongHom.exists_chart_inter_preimage c T.hasAllLocalDomains
      k m l hkm (fun _ h => ((hmem l hl).2.1 h).2)
  choose q hq using key
  refine ⟨{k' | ∃ l hl, q l hl = k'}, hτ.dependent_image q, ?_, c.baseMap ⁻¹' N,
    c.baseMap.continuous.continuousAt.preimage_mem_nhds hN, ?_⟩
  · rintro _ ⟨l, hl, rfl⟩
    rw [hq l hl]
    refine ⟨⟨hy, (hmem l hl).1⟩, fun z hz => ⟨hz.1, ((hmem l hl).2.1 hz.2).1⟩, trivial⟩
  · rintro z ⟨⟨hzk, hzj⟩, hzN⟩
    have hzm : c.baseMap z ∈ Set.range (B.presentation.atlas.chart m) := hkm ⟨z, hzk, rfl⟩
    obtain ⟨l, hl, hzl⟩ := Set.mem_iUnion₂.mp (hcov ⟨⟨hzj, hzm⟩, hzN⟩)
    refine Set.mem_iUnion₂.mpr ⟨q l hl, ⟨l, hl, rfl⟩, ?_⟩
    rw [hq l hl]
    exact ⟨hzk, hzl⟩

/-- The preimage of a target chart is locally chart covered at its points. -/
theorem isLocallyChartCovered_preimage (c : T ⟶ B) (j : B.presentation.atlas.Index)
    {y : T.presentation.space} (hyj : c.baseMap y ∈ Set.range (B.presentation.atlas.chart j)) :
    T.IsLocallyChartCovered (fun _ => True)
      (c.baseMap ⁻¹' Set.range (B.presentation.atlas.chart j)) y := by
  classical
  obtain ⟨σ, hσfin, hσ, hyσ, hσn⟩ := T.presentation.atlas.isNet_chartFamily.1 y
  have key : ∀ V ∈ σ, ∃ k : T.presentation.atlas.Index,
      Set.range (T.presentation.atlas.chart k) = V := fun V hV => hσ hV
  choose k hk using key
  have : Finite σ := hσfin.to_subtype
  refine isLocallyChartCovered_of_cover
    (Zs := fun V : σ => Set.range (T.presentation.atlas.chart (k V.1 V.2)) ∩
      c.baseMap ⁻¹' Set.range (B.presentation.atlas.chart j))
    (fun V => Set.inter_subset_right) hσn ?_ fun V => ?_
  · rintro z ⟨hzj, V, hV, hzV⟩
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, (hk V hV).symm ▸ hzV, hzj⟩
  · obtain ⟨m, hm⟩ := c.target_exists (k V.1 V.2)
    exact isLocallyChartCovered_chart_inter_preimage c _ m hm j
      ((hk V.1 V.2).symm ▸ hyσ V.1 V.2) hyj

end LocalCovers

section Gluing

variable {S A : SaturatedAtlasPresentation.{u, v, w} K}

/-- **Gluing equality along a refinement.** Let `x₀ x₁ x₂ : S ⟶ A`, let `L` be a Hausdorff set
of points of `A` covered by finitely many charts `C ⊆ L` and containing the image of `x₀`.
Suppose the three maps have the same preimages of the charts of `C`, and `x₁, x₂` have the same
pullbacks on every chart of `S` which `x₀` maps into a chart of `C`. Then `x₁` and `x₂` become
equal in the localized category. -/
theorem localizationFunctor_map_eq_of_local_eq (x₀ x₁ x₂ : S ⟶ A)
    (L : Set A.presentation.space) [T2Space L] (C : Finset A.presentation.atlas.Index)
    (hCL : ∀ c ∈ C, Set.range (A.presentation.atlas.chart c) ⊆ L)
    (hLC : L ⊆ ⋃ c ∈ C, Set.range (A.presentation.atlas.chart c))
    (hx₀ : ∀ z, x₀.baseMap z ∈ L)
    (hpre₁ : ∀ c ∈ C, x₀.baseMap ⁻¹' Set.range (A.presentation.atlas.chart c) =
      x₁.baseMap ⁻¹' Set.range (A.presentation.atlas.chart c))
    (hpre₂ : ∀ c ∈ C, x₀.baseMap ⁻¹' Set.range (A.presentation.atlas.chart c) =
      x₂.baseMap ⁻¹' Set.range (A.presentation.atlas.chart c))
    (heq : ∀ (P : S.presentation.atlas.Index) (c : A.presentation.atlas.Index), c ∈ C →
      (h₁ : x₁.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
        Set.range (A.presentation.atlas.chart c)) →
      (h₂ : x₂.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
        Set.range (A.presentation.atlas.chart c)) →
      Set.range (S.presentation.atlas.chart P) ⊆
        x₀.baseMap ⁻¹' Set.range (A.presentation.atlas.chart c) →
      x₁.pullback P c h₁ = x₂.pullback P c h₂) :
    localizationFunctor.map x₁ = localizationFunctor.map x₂ := by
  classical
  let Q : S.presentation.atlas.Index → Prop := fun P =>
    ∃ c ∈ C, Set.range (S.presentation.atlas.chart P) ⊆
      x₀.baseMap ⁻¹' Set.range (A.presentation.atlas.chart c)
  -- local covers of a source chart by good charts
  have hlocal : ∀ (P₀ : S.presentation.atlas.Index) (y : S.presentation.space),
      y ∈ Set.range (S.presentation.atlas.chart P₀) →
        S.IsLocallyChartCovered Q (Set.range (S.presentation.atlas.chart P₀)) y := by
    intro P₀ y hy
    let Cy : Set A.presentation.atlas.Index :=
      {c | c ∈ C ∧ x₀.baseMap y ∈ Set.range (A.presentation.atlas.chart c)}
    have hCy : Cy.Finite := C.finite_toSet.subset fun c hc => hc.1
    have : Finite Cy := hCy.to_subtype
    let x₀L : S.presentation.space → L := fun z => ⟨x₀.baseMap z, hx₀ z⟩
    have hx₀L : Continuous x₀L := x₀.baseMap.continuous.subtype_mk _
    let O : Set L := ⋂ c ∈ C.filter
      (fun c => x₀.baseMap y ∉ Set.range (A.presentation.atlas.chart c)),
        (Subtype.val ⁻¹' Set.range (A.presentation.atlas.chart c))ᶜ
    have hO : IsOpen O := by
      refine isOpen_biInter_finset fun c hc => ?_
      refine isOpen_compl_iff.mpr (IsCompact.isClosed ?_)
      have hcomp := (A.presentation.atlas.isEmbedding_chart c).continuous
      refine (Topology.IsInducing.subtypeVal.isCompact_preimage_iff ?_).mpr
        (isCompact_range hcomp)
      rw [Subtype.range_coe]
      exact hCL c (Finset.mem_filter.mp hc).1
    have hyO : x₀L y ∈ O := by
      refine Set.mem_iInter₂.mpr fun c hc => ?_
      exact (Finset.mem_filter.mp hc).2
    refine isLocallyChartCovered_of_cover
      (Zs := fun c : Cy => Set.range (S.presentation.atlas.chart P₀) ∩
        x₀.baseMap ⁻¹' Set.range (A.presentation.atlas.chart c.1))
      (fun c => Set.inter_subset_left) ((hO.preimage hx₀L).mem_nhds hyO) ?_ fun c => ?_
    · rintro z ⟨hzP, hzO⟩
      obtain ⟨c, hc, hzc⟩ := Set.mem_iUnion₂.mp (hLC (hx₀ z))
      by_cases hyc : x₀.baseMap y ∈ Set.range (A.presentation.atlas.chart c)
      · exact Set.mem_iUnion.mpr ⟨⟨c, hc, hyc⟩, hzP, hzc⟩
      · exact absurd hzc (Set.mem_iInter₂.mp hzO c (Finset.mem_filter.mpr ⟨hc, hyc⟩))
    · refine ((isLocallyChartCovered_chart P₀ hy).inter
        (isLocallyChartCovered_preimage x₀ c.1 c.2.2)).of_subset_pred fun k hk => ?_
      exact ⟨c.1, c.2.1, hk.trans Set.inter_subset_right⟩
  let G : S.presentation.atlas.RefiningSelection :=
    { carrier := {P | Q P}
      downward_closed := fun i j hij hj => by
        obtain ⟨c, hc, hjc⟩ := hj
        exact ⟨c, hc, hij.trans hjc⟩
      locally_refining := by
        rintro U ⟨P₀, rfl⟩ y hy
        obtain ⟨σ, hσ, hmem, N, hN, hcov⟩ := hlocal P₀ y hy
        refine ⟨(fun k => Set.range (S.presentation.atlas.chart k)) '' σ, hσ.image _, ?_, ?_, ?_⟩
        · rintro _ ⟨k, hk, rfl⟩
          exact ⟨⟨k, (hmem k hk).2.2⟩, rfl⟩
        · rintro _ ⟨k, hk, rfl⟩
          exact ⟨(hmem k hk).2.1, (hmem k hk).1⟩
        · rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
          refine ⟨N, hN, fun z hz => ?_⟩
          obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp (hcov ⟨hz.2, hz.1⟩)
          exact ⟨_, ⟨k, hk, rfl⟩, hzk⟩ }
  have himage : ∀ (P : S.presentation.atlas.Index) (c : A.presentation.atlas.Index), c ∈ C →
      Set.range (S.presentation.atlas.chart P) ⊆
        x₀.baseMap ⁻¹' Set.range (A.presentation.atlas.chart c) →
      x₁.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
          Set.range (A.presentation.atlas.chart c) ∧
        x₂.baseMap '' Set.range (S.presentation.atlas.chart P) ⊆
          Set.range (A.presentation.atlas.chart c) := by
    intro P c hc hPc
    constructor
    · rintro _ ⟨z, hz, rfl⟩
      have := hPc hz
      rw [hpre₁ c hc] at this
      exact this
    · rintro _ ⟨z, hz, rfl⟩
      have := hPc hz
      rw [hpre₂ c hc] at this
      exact this
  have hbase : x₁.baseMap = x₂.baseMap := by
    ext y
    obtain ⟨P₀, hP₀⟩ := exists_chart_mem S y
    obtain ⟨σ, -, hmem, N, hN, hcov⟩ := hlocal P₀ y hP₀
    obtain ⟨P, hP, hyP⟩ := Set.mem_iUnion₂.mp (hcov ⟨hP₀, mem_of_mem_nhds hN⟩)
    obtain ⟨c, hc, hPc⟩ := (hmem P hP).2.2
    obtain ⟨h₁, h₂⟩ := himage P c hc hPc
    obtain ⟨p, rfl⟩ := hyP
    rw [← x₁.chart_comm P c h₁ p, ← x₂.chart_comm P c h₂ p, heq P c hc h₁ h₂ hPc]
  have hr := isQuasiIso_refiningSubatlasInclusion G
  have hrx : S.refiningSubatlasInclusion G ≫ x₁ = S.refiningSubatlasInclusion G ≫ x₂ := by
    refine AffinoidAtlasPresentation.StrongHom.ext_of_saturated
      (S.refiningSubpresentation G).hasAllLocalDomains ?_ fun i => ?_
    · change x₁.baseMap.comp (ContinuousMap.id _) = x₂.baseMap.comp (ContinuousMap.id _)
      rw [hbase]
    · obtain ⟨c, hc, hic⟩ := i.2
      obtain ⟨h₁, h₂⟩ := himage i.val c hc hic
      have h₁' : (S.refiningSubatlasInclusion G ≫ x₁).baseMap ''
          Set.range ((S.refiningSubpresentation G).presentation.atlas.chart i) ⊆
            Set.range (A.presentation.atlas.chart c) := h₁
      refine ⟨c, h₁', ?_⟩
      rw [refiningSubatlasInclusion_comp_pullback x₁ G i c h₁ h₁',
        refiningSubatlasInclusion_comp_pullback x₂ G i c h₂, heq i.val c hc h₁ h₂ hic]
  have : IsIso (localizationFunctor.map (S.refiningSubatlasInclusion G)) :=
    Localization.inverts localizationFunctor (quasiIsomorphisms (K := K)) _ hr
  have h := congrArg (fun f => localizationFunctor.map f) hrx
  simp only [Functor.map_comp] at h
  exact (cancel_epi (localizationFunctor.map (S.refiningSubatlasInclusion G))).1 h

end Gluing

end Langlands.Analytic.SaturatedAtlasPresentation
