import Langlands.Geometry.Analytic.QuasiEtaleRigidity.ChartCoverRigidity
import Langlands.Geometry.Analytic.KeyLemma.ChartTestTransfer
import Langlands.Geometry.Analytic.KeyLemma.QuasiEtaleLiftChartCover
import Langlands.Geometry.Analytic.KeyLemma.StrongNearLifts
import Langlands.Geometry.Analytic.SaturatedLiteralDomainGluing
import Langlands.Geometry.Analytic.QuotientChartRepresentatives
import Langlands.Geometry.Analytic.LocalizedPullbackDescent
import Langlands.Geometry.Analytic.QuasiEtaleRigidity.QuasiEtaleRigid
import Langlands.Geometry.Analytic.SaturatedDomainSite
import Langlands.Geometry.Analytic.SaturatedDomainPreimage
import Langlands.Geometry.Analytic.AtlasTopology.RefinementComposition
import Langlands.Geometry.Analytic.AtlasTopology.DomainIntersections

/-! # Near lifts along quasi-étale maps, at the level of strong maps -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Set AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

section Locality

variable {S T : SaturatedAtlasPresentation.{u, v, w} K} {ι : Type z}

/-- Equal strong maps have equal pullbacks, whatever the admissibility proofs. -/
theorem pullback_eq_of_eq {f f' : S ⟶ T} (h : f = f') (i : S.presentation.atlas.Index)
    (j : T.presentation.atlas.Index)
    (hf : f.baseMap '' range (S.presentation.atlas.chart i) ⊆ range (T.presentation.atlas.chart j))
    (hf' : f'.baseMap '' range (S.presentation.atlas.chart i) ⊆
      range (T.presentation.atlas.chart j)) :
    f.pullback i j hf = f'.pullback i j hf' :=
  pullback_congr h i j hf hf'

/-- Restricting from a domain to a smaller one and then including is the inclusion of the
smaller domain, after composing with any strong map. -/
theorem originalDomainStrongMap_comp_inclusion_comp
    {U V : S.presentation.atlas.OriginalChartDomain} (hUV : U ≤ V) (f : S ⟶ T) :
    (S.presentation.originalDomainStrongMap hUV : S.originalDomain U ⟶ S.originalDomain V) ≫
        (S.originalDomainInclusion V ≫ f) = S.originalDomainInclusion U ≫ f := by
  have h2 := originalDomainStrongMap_comp_eq_restrictOriginalDomain (A := S) (B := T) hUV
    (f.restrictSubspace V.carrier V.is_domain)
  rw [originalDomainInclusion_comp_eq_restrictSubspace V f]
  exact h2.trans ((StrongHom.restrictSubspace_restrictOriginalDomain f hUV).trans
    (originalDomainInclusion_comp_eq_restrictSubspace U f).symm)

/-- Strong maps that agree on every member of a domain family containing every source chart
are equal. -/
theorem eq_of_originalDomainCover {D : ι → S.presentation.atlas.OriginalChartDomain}
    (hD : OriginalDomainCoversCharts D) {a b : S ⟶ T}
    (h : ∀ k, S.originalDomainInclusion (D k) ≫ a = S.originalDomainInclusion (D k) ≫ b) :
    a = b := by
  have ha := StrongHom.toOriginalDomainStrongMatchingFamily_glue a D hD
  have hb := StrongHom.toOriginalDomainStrongMatchingFamily_glue b D hD
  have he : StrongHom.toOriginalDomainStrongMatchingFamily a D =
      StrongHom.toOriginalDomainStrongMatchingFamily b D := by
    apply OriginalDomainStrongMatchingFamily.ext
    funext k
    have hk := h k
    rw [originalDomainInclusion_comp_eq_restrictSubspace,
      originalDomainInclusion_comp_eq_restrictSubspace] at hk
    exact hk
  rw [← ha, ← hb, he]

/-- **Locality of the test relation.** If two strong maps satisfy the test relation on every
member of a domain family containing every source chart, they satisfy it globally. -/
theorem StrongNear.of_originalDomainCover {D : ι → S.presentation.atlas.OriginalChartDomain}
    (hD : OriginalDomainCoversCharts D) {τ : TestTriple T} {a b : S ⟶ T}
    (h : ∀ k, StrongNear τ (S.originalDomainInclusion (D k) ≫ a)
      (S.originalDomainInclusion (D k) ≫ b)) :
    StrongNear τ a b := by
  have h' : ∀ k, StrongNear τ
      (show S.originalDomain (D k) ⟶ T from a.restrictSubspace (D k).carrier (D k).is_domain)
      (show S.originalDomain (D k) ⟶ T from b.restrictSubspace (D k).carrier (D k).is_domain) :=
    fun k => by
      have := h k
      rwa [originalDomainInclusion_comp_eq_restrictSubspace,
        originalDomainInclusion_comp_eq_restrictSubspace] at this
  refine ⟨?_, ?_, ?_⟩
  · ext z
    obtain ⟨i, hi⟩ := exists_chart_mem S z
    obtain ⟨k, hk⟩ := hD i
    exact Set.ext_iff.mp (h' k).1 ⟨z, hk hi⟩
  · intro z hz
    obtain ⟨i, hi⟩ := exists_chart_mem S z
    obtain ⟨k, hk⟩ := hD i
    obtain ⟨j, hj, p, hp⟩ := (h' k).2.1 ⟨z, hk hi⟩ hz
    refine ⟨j.val, ⟨?_, ?_⟩, ⟨p, congrArg Subtype.val hp⟩⟩
    · rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      exact hj.1 ⟨_, ⟨q, rfl⟩, rfl⟩
    · rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      exact hj.2 ⟨_, ⟨q, rfl⟩, rfl⟩
  · intro i hi p
    obtain ⟨k, hk⟩ := hD i
    let j : (S.originalDomain (D k)).presentation.atlas.Index := ⟨i, fun _ hx => hk hx⟩
    have hj : IsTestPiece τ
        (show S.originalDomain (D k) ⟶ T from a.restrictSubspace (D k).carrier (D k).is_domain)
        (show S.originalDomain (D k) ⟶ T from b.restrictSubspace (D k).carrier (D k).is_domain)
        j := by
      constructor
      · rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
        exact hi.1 ⟨_, ⟨q, rfl⟩, rfl⟩
      · rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
        exact hi.2 ⟨_, ⟨q, rfl⟩, rfl⟩
    exact (h' k).2.2 j hj p

/-- The charts that a strong map sends into some member of a family of charts whose ranges
locally refine the target locally refine the whole source. -/
theorem locallyRefines_charts_into (x : S ⟶ T) {κ : Type z}
    (c : κ → T.presentation.atlas.Index)
    (hc : AtlasTopology.LocallyRefines
      (range fun k => range (T.presentation.atlas.chart (c k))) {univ}) :
    AtlasTopology.LocallyRefines
      (range fun q : {q : κ × S.presentation.atlas.Index //
          x.baseMap '' range (S.presentation.atlas.chart q.2) ⊆
            range (T.presentation.atlas.chart (c q.1))} =>
        range (S.presentation.atlas.chart q.val.2)) {univ} := by
  have h1 := (hc.preimage x.baseMap x.baseMap.continuous).mono subset_rfl
    (show ({univ} : Set (Set S.presentation.space)) ⊆ _ by
      rintro _ rfl
      exact ⟨univ, rfl, preimage_univ⟩)
  refine h1.trans ?_
  rintro _ ⟨_, ⟨k, rfl⟩, rfl⟩ y hy
  have hdom := StrongHom.isOriginalChartDomain_preimage x S.hasAllLocalDomains
    (IndexedAffinoidAtlas.OriginalChartDomain.ofChart (c k))
  obtain ⟨σ, hf, hσ, hm, hn⟩ :=
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hdom _ (mem_singleton _) y hy
  refine ⟨σ, hf, ?_, hm, hn⟩
  intro V hV
  obtain ⟨i, rfl⟩ := hσ hV
  exact ⟨⟨(k, i), image_subset_iff.mpr (hm _ hV).1⟩, rfl⟩

end Locality

section Lifts

variable {A B : AffinoidAtlasPresentation.{u, v, v} K}

/-- **Gluing of chartwise near lifts.** A strong map with a finite cover by lift charts and a
rigid localization has near lifts at the level of strong maps. -/
theorem hasStrongNearLifts_of_liftCharts [T2Space (ofSaturation A).presentation.space]
    (g : ofSaturation A ⟶ ofSaturation B) (hlift : HasFiniteLiftChartCover g)
    (hrig : IsRigid (localizationFunctor.map g)) : HasStrongNearLifts g := by
  classical
  intro E
  obtain ⟨s, hs, hcov⟩ := hlift
  obtain ⟨Erig, hErig⟩ := hrig
  let E' : Finset (TestTriple (ofSaturation A)) := E ∪ Erig
  choose F ε hε hFε using fun c : ↥(s : Set (ofSaturation A).presentation.atlas.Index) =>
    exists_globalChart_tests_strongNear c.val E'
  choose w hcw H using fun c : ↥(s : Set (ofSaturation A).presentation.atlas.Index) =>
    hs c.val c.property
  choose G δ hδ hG using fun c : ↥(s : Set (ofSaturation A).presentation.atlas.Index) =>
    H c (F c) (ε c) (hε c)
  let τ₀ : ↥(s : Set (ofSaturation A).presentation.atlas.Index) → TestTriple (ofSaturation B) :=
    fun c => ⟨w c, 0, 1, one_pos⟩
  let τh : (c : ↥(s : Set (ofSaturation A).presentation.atlas.Index)) →
      (ofSaturation B).presentation.atlas.algebra (w c) → TestTriple (ofSaturation B) :=
    fun c h => ⟨w c, h, δ c, hδ c⟩
  let Dc : ↥(s : Set (ofSaturation A).presentation.atlas.Index) →
      Finset (TestTriple (ofSaturation B)) :=
    fun c => insert (τ₀ c) ((G c).image (τh c))
  refine ⟨s.attach.biUnion fun c => Dc ⟨c.val, c.property⟩, fun S x y hD => ?_⟩
  have hmemD : ∀ c : ↥(s : Set (ofSaturation A).presentation.atlas.Index), ∀ τ ∈ Dc c,
      StrongNear τ y (x ≫ g) := fun c τ hτ =>
    hD τ (Finset.mem_biUnion.mpr ⟨⟨c.val, c.property⟩, Finset.mem_attach _ _, hτ⟩)
  -- The charts of `S` sent into a lift chart.
  let ι := {q : ↥(s : Set (ofSaturation A).presentation.atlas.Index) × S.presentation.atlas.Index //
    x.baseMap '' range (S.presentation.atlas.chart q.2) ⊆
      range ((ofSaturation A).presentation.atlas.chart q.1.val)}
  have hxg : ∀ q : ι, (x ≫ g).baseMap '' range (S.presentation.atlas.chart q.val.2) ⊆
      range ((ofSaturation B).presentation.atlas.chart (w q.val.1)) := by
    rintro q _ ⟨z, hz, rfl⟩
    exact hcw q.val.1 ⟨x.baseMap z, q.property ⟨z, hz, rfl⟩, rfl⟩
  have hy : ∀ q : ι, y.baseMap '' range (S.presentation.atlas.chart q.val.2) ⊆
      range ((ofSaturation B).presentation.atlas.chart (w q.val.1)) := by
    rintro q _ ⟨z, hz, rfl⟩
    have hz' : z ∈ (x ≫ g).baseMap ⁻¹' (τ₀ q.val.1).locus := hxg q ⟨z, hz, rfl⟩
    rw [← (hmemD q.val.1 _ (Finset.mem_insert_self _ _)).1] at hz'
    exact hz'
  have hclose : ∀ q : ι, ∀ h ∈ G q.val.1,
      ∀ p : BanachSpectrum (S.presentation.atlas.algebra q.val.2),
        p (y.pullback q.val.2 (w q.val.1) (hy q) h -
          (x ≫ g).pullback q.val.2 (w q.val.1) (hxg q) h) ≤ δ q.val.1 :=
    fun q h hh p => (hmemD q.val.1 _ (Finset.mem_insert_of_mem
      (Finset.mem_image_of_mem (τh q.val.1) hh))).2.2 q.val.2 ⟨hy q, hxg q⟩ p
  choose a ha₁ ha₂ using fun q : ι =>
    hG q.val.1 S x y q.val.2 q.property (hxg q) (hy q) (hclose q)
  -- The chartwise lifts.
  let Dq : ι → S.presentation.atlas.OriginalChartDomain :=
    fun q => IndexedAffinoidAtlas.OriginalChartDomain.ofChart q.val.2
  let P₀ : (q : ι) → (S.originalDomain (Dq q)).presentation.atlas.Index :=
    fun q => ⟨q.val.2, fun _ hz => hz⟩
  have hglob : ∀ q : ι,
      range ((S.originalDomain (Dq q)).presentation.atlas.chart (P₀ q)) = univ := by
    intro q
    refine eq_univ_of_forall fun z => ?_
    obtain ⟨p, hp⟩ := z.property
    exact ⟨p, Subtype.ext hp⟩
  let χ : (q : ι) → S.originalDomain (Dq q) ⟶ ofSaturation A :=
    fun q => chartSourceMap (P₀ q) (hglob q) q.val.1.val (a q)
  -- The lifts lie over `y`.
  have hP1 : ∀ q : ι, χ q ≫ g = S.originalDomainInclusion (Dq q) ≫ y := by
    intro q
    have hi : (show S.originalDomain (Dq q) ⟶ ofSaturation B from
          y.restrictSubspace (Dq q).carrier (Dq q).is_domain).baseMap ''
        range ((S.originalDomain (Dq q)).presentation.atlas.chart (P₀ q)) ⊆
          range ((ofSaturation B).presentation.atlas.chart (w q.val.1)) := by
      rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      exact hy q ⟨_, ⟨p, rfl⟩, rfl⟩
    refine (chartSourceMap_comp (P₀ q) (hglob q) q.val.1.val (a q) g (w q.val.1)
      (hcw q.val.1)).trans ?_
    refine (congrArg (chartSourceMap (P₀ q) (hglob q) (w q.val.1)) (ha₁ q)).trans ?_
    refine Eq.trans ?_ (originalDomainInclusion_comp_eq_restrictSubspace (Dq q) y).symm
    exact chartSourceMap_eq (P₀ q) (hglob q) (w q.val.1)
      (y.restrictSubspace (Dq q).carrier (Dq q).is_domain) hi
  -- The lifts are near `x`.
  have hP2 : ∀ q : ι, ∀ τ ∈ E', StrongNear τ (χ q) (S.originalDomainInclusion (Dq q) ≫ x) := by
    intro q
    have ha := chartSourceMap_admissible (P₀ q) (hglob q) q.val.1.val (a q) (P₀ q)
    have hb : (S.originalDomainInclusion (Dq q) ≫ x).baseMap ''
        range ((S.originalDomain (Dq q)).presentation.atlas.chart (P₀ q)) ⊆
          range ((ofSaturation A).presentation.atlas.chart q.val.1.val) := by
      rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩
      exact q.property ⟨_, ⟨p, rfl⟩, rfl⟩
    have hb' : (x.restrictSubspace (Dq q).carrier (Dq q).is_domain :
          S.originalDomain (Dq q) ⟶ ofSaturation A).baseMap ''
        range ((S.originalDomain (Dq q)).presentation.atlas.chart (P₀ q)) ⊆
          range ((ofSaturation A).presentation.atlas.chart q.val.1.val) := hb
    refine hFε q.val.1 (S.originalDomain (Dq q)) (P₀ q) (hglob q) (χ q)
      (S.originalDomainInclusion (Dq q) ≫ x) ha hb fun h hh p => ?_
    rw [chartSourceMap_pullback_global (P₀ q) (hglob q) q.val.1.val (a q) ha,
      pullback_eq_of_eq (originalDomainInclusion_comp_eq_restrictSubspace (Dq q) x)
        (P₀ q) q.val.1.val hb hb']
    exact ha₂ q h hh p
  -- Overlaps, by rigidity.
  have hover : ∀ q q' : ι,
      StrongHom.restrictOriginalDomain (A := S.presentation)
          (B := (ofSaturation A).presentation) (χ q) (inf_le_left : Dq q ⊓ Dq q' ≤ Dq q) =
        StrongHom.restrictOriginalDomain (A := S.presentation)
          (B := (ofSaturation A).presentation) (χ q') (inf_le_right : Dq q ⊓ Dq q' ≤ Dq q') := by
    intro q q'
    let j : S.originalDomain (Dq q ⊓ Dq q') ⟶ S.originalDomain (Dq q) :=
      S.presentation.originalDomainStrongMap inf_le_left
    let j' : S.originalDomain (Dq q ⊓ Dq q') ⟶ S.originalDomain (Dq q') :=
      S.presentation.originalDomainStrongMap inf_le_right
    refine (originalDomainStrongMap_comp_eq_restrictOriginalDomain inf_le_left (χ q)).symm.trans
      ((?_ : j ≫ χ q = j' ≫ χ q').trans
        (originalDomainStrongMap_comp_eq_restrictOriginalDomain inf_le_right (χ q')))
    have hcomp : localizationFunctor.map (j ≫ χ q) ≫ localizationFunctor.map g =
        localizationFunctor.map (j' ≫ χ q') ≫ localizationFunctor.map g := by
      rw [← Functor.map_comp, ← Functor.map_comp, Category.assoc, Category.assoc, hP1 q, hP1 q',
        originalDomainStrongMap_comp_inclusion_comp, originalDomainStrongMap_comp_inclusion_comp]
    have hnear₁ : ∀ τ ∈ Erig, StrongNear τ (S.originalDomainInclusion (Dq q ⊓ Dq q') ≫ x)
        (j ≫ χ q) := by
      intro τ hτ
      have := (hP2 q τ (Finset.mem_union_right _ hτ)).precomp j
      rw [originalDomainStrongMap_comp_inclusion_comp] at this
      exact this.symm
    have hnear₂ : ∀ τ ∈ Erig, StrongNear τ (S.originalDomainInclusion (Dq q ⊓ Dq q') ≫ x)
        (j' ≫ χ q') := by
      intro τ hτ
      have := (hP2 q' τ (Finset.mem_union_right _ hτ)).precomp j'
      rw [originalDomainStrongMap_comp_inclusion_comp] at this
      exact this.symm
    apply localizationFunctor_map_injective
    exact hErig (localizationFunctor.obj (S.originalDomain (Dq q ⊓ Dq q')))
      (localizationFunctor.map (S.originalDomainInclusion (Dq q ⊓ Dq q') ≫ x))
      (localizationFunctor.map (j ≫ χ q)) (localizationFunctor.map (j' ≫ χ q')) hcomp
      fun τ hτ => ⟨isNear_localizationFunctor_map (X := localizationFunctor.obj (ofSaturation A))
        (hnear₁ τ hτ), isNear_localizationFunctor_map
          (X := localizationFunctor.obj (ofSaturation A)) (hnear₂ τ hτ)⟩
  -- Gluing.
  let d : S.presentation.OriginalDomainStrongMatchingFamily (ofSaturation A).presentation Dq :=
    { localMap := χ, overlap := hover }
  have hDcov : AtlasTopology.LocallyRefines (range fun q : ι => (Dq q).carrier) {univ} :=
    locallyRefines_charts_into x (fun c : ↥(s : Set (ofSaturation A).presentation.atlas.Index) =>
      c.val) hcov
  let sel := domainCoverSourceSelection Dq hDcov
  let D' : ι → (S.refiningSubpresentation sel).presentation.atlas.OriginalChartDomain :=
    fun q => S.presentation.atlas.originalDomainSubatlasOrderIso sel.carrier
      sel.locally_refining (Dq q)
  have hD' : OriginalDomainCoversCharts D' := domainCoverSourceSelection_coversCharts Dq hDcov
  let x' : S.refiningSubpresentation sel ⟶ ofSaturation A := d.refinedGlue hDcov
  have hloc : ∀ q : ι, (S.refiningSubpresentation sel).originalDomainInclusion (D' q) ≫ x' =
      originalDomainRefiningMap sel (Dq q) ≫ χ q := by
    intro q
    erw [originalDomainInclusion_comp_eq_restrictSubspace, originalDomainRefiningMap_comp]
    exact d.refinedGlue_restrictSubspace hDcov q
  refine ⟨S.refiningSubpresentation sel, S.refiningSubatlasInclusion sel,
    isQuasiIso_refiningSubatlasInclusion sel, x', ?_, ?_⟩
  · refine eq_of_originalDomainCover hD' fun q => ?_
    have e := originalDomainRefiningMap_inclusion (A := S) sel (Dq q)
    calc (S.refiningSubpresentation sel).originalDomainInclusion (D' q) ≫ x' ≫ g
        = (originalDomainRefiningMap sel (Dq q) ≫ χ q) ≫ g := by
          rw [← hloc q, Category.assoc]
      _ = originalDomainRefiningMap sel (Dq q) ≫ S.originalDomainInclusion (Dq q) ≫ y := by
          rw [Category.assoc, hP1 q]
      _ = (S.refiningSubpresentation sel).originalDomainInclusion (D' q) ≫
            S.refiningSubatlasInclusion sel ≫ y := by
          rw [← Category.assoc, e, Category.assoc]
  · intro τ hτ
    refine StrongNear.of_originalDomainCover hD' fun q => ?_
    have e := originalDomainRefiningMap_inclusion (A := S) sel (Dq q)
    rw [hloc q, ← Category.assoc, ← e, Category.assoc]
    exact (hP2 q τ (Finset.mem_union_left _ hτ)).precomp _

/-- **Existence in Berkovich's Key Lemma 7.2 for strong maps.** A quasi-étale strong map with
compact Hausdorff source has near lifts at the level of strong maps. -/
theorem IsQuasiEtale.hasStrongNearLifts {g : ofSaturation A ⟶ ofSaturation B}
    (hg : IsQuasiEtale g) [CompactSpace A.space] [T2Space A.space] :
    HasStrongNearLifts g := by
  let : T2Space (ofSaturation A).presentation.space := ‹T2Space A.space›
  exact hasStrongNearLifts_of_liftCharts g hg.hasFiniteLiftChartCover
    (isRigid_of_quasiEtale (localizationFunctor.map g) ⟨A, B, g, hg, ⟨Iso.refl _⟩⟩
      ⟨‹CompactSpace A.space›, ‹T2Space A.space›⟩)

end Lifts

end Langlands.Analytic.SaturatedAtlasPresentation
