import Langlands.Geometry.Analytic.FullRecognitionPairSystems
import Langlands.Geometry.Analytic.StrongSourceRestriction

/-! # Composition of full-recognition pair systems -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (b : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Finitely many original charts, each contained in the chart `i` and in the
recognized subset `W`, whose ranges cover `S`. -/
structure RecognizedChartCover (i : b.Index) (W : b.RecognizedSubset) (S : Set X) where
  size : ℕ
  index : Fin size → b.Index
  subset_chart : ∀ m, Set.range (b.chart (index m)) ⊆ Set.range (b.chart i)
  subset_recognized : ∀ m, Set.range (b.chart (index m)) ⊆ W.locus
  covers : S ⊆ ⋃ m, Set.range (b.chart (index m))

/-- A compact subset of an original chart that lies in a recognized subset is
covered by the original components of finitely many recognized subsets
contained in both, chosen through the net axiom of the recognition atlas. -/
def recognizedChartCover (i : b.Index) (W : b.RecognizedSubset)
    (S : Set X) (hS : IsCompact S) (hSi : S ⊆ Set.range (b.chart i))
    (hSW : S ⊆ W.locus) : b.RecognizedChartCover i W S := by
  classical
  have hsub : S ⊆ Set.range (b.recognitionAtlas.chart (b.originalRecognitionIndex i)) ∩
      Set.range (b.recognitionAtlas.chart W) := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [b.recognitionAtlas_original_range]
      exact hSi hx
    · exact (RecognizedSubset.range_chart W).symm.subset (hSW hx)
  let c := b.recognitionAtlas.compactIntersectionChartCover
    (b.originalRecognitionIndex i) W S hS hsub
  let Ut : Fin c.size → b.RecognizedSubset := fun t => c.index t
  let ι := Σ t : Fin c.size, Fin (Ut t).property.cover.size
  let F : ι → b.Index := fun s => (Ut s.1).property.cover.index s.2
  let e := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun m => F (e m), ?_, ?_, ?_⟩
  · intro m
    have h1 := RecognizedSubset.component_subset (Ut (e m).1) (e m).2
    have h2 := c.left_subset (e m).1
    rw [b.recognitionAtlas_original_range] at h2
    exact h1.trans ((RecognizedSubset.range_chart (Ut (e m).1)).symm.subset.trans h2)
  · intro m
    have h1 := RecognizedSubset.component_subset (Ut (e m).1) (e m).2
    have h3 := c.right_subset (e m).1
    exact h1.trans ((RecognizedSubset.range_chart (Ut (e m).1)).symm.subset.trans
      (h3.trans (RecognizedSubset.range_chart W).subset))
  · intro x hx
    obtain ⟨t, ht⟩ := c.covers x hx
    have hx1 : x ∈ ⋃ p, Set.range (b.chart ((Ut t).property.cover.index p)) :=
      (Ut t).property.cover_locus.symm.subset
        ((RecognizedSubset.range_chart (Ut t)).subset ht)
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hx1
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨t, p⟩, ?_⟩
    rw [e.apply_symm_apply]
    exact hp

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

section SourceCover

variable {P Q : AffinoidAtlasPresentation.{u, v, w} K} (h : StrongHom P Q)

theorem isCompact_image_chart (k : P.atlas.Index) :
    IsCompact (h.baseMap '' Set.range (P.atlas.chart k)) :=
  (isCompact_range (P.atlas.isEmbedding_chart k).continuous).image h.baseMap.continuous

/-- Original target charts inside `T0` and inside the recognized subset `W`
covering the image of the source chart `k`. -/
def recognizedTargetChartCover (k : P.atlas.Index) (T0 : Q.atlas.Index)
    (hT0 : h.baseMap '' Set.range (P.atlas.chart k) ⊆ Set.range (Q.atlas.chart T0))
    (W : Q.atlas.RecognizedSubset)
    (hW : h.baseMap '' Set.range (P.atlas.chart k) ⊆ W.locus) :
    Q.atlas.RecognizedChartCover T0 W (h.baseMap '' Set.range (P.atlas.chart k)) :=
  Q.atlas.recognizedChartCover T0 W _ (h.isCompact_image_chart k) hT0 hW

/-- The actual finite domain cover of the whole source chart algebra by the
inverse images, under the bounded pullback into `T0`, of the restriction
domains of these target charts. -/
def recognizedSourceDomainCover (k : P.atlas.Index) (T0 : Q.atlas.Index)
    (hT0 : h.baseMap '' Set.range (P.atlas.chart k) ⊆ Set.range (Q.atlas.chart T0))
    (W : Q.atlas.RecognizedSubset)
    (hW : h.baseMap '' Set.range (P.atlas.chart k) ⊆ W.locus) :
    Domain.FiniteCover (Domain.whole K (P.atlas.algebra k)) where
  size := (h.recognizedTargetChartCover k T0 hT0 W hW).size
  obj m := Domain.pullback (h.pullback k T0 hT0)
    (Q.atlas.restrictionDomain ((h.recognizedTargetChartCover k T0 hT0 W hW).index m) T0
      ((h.recognizedTargetChartCover k T0 hT0 W hW).subset_chart m))
  map m := ⟨_, BoundedAlgHom.comp_id _⟩
  covers x _ := by
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp
      ((h.recognizedTargetChartCover k T0 hT0 W hW).covers ⟨_, Set.mem_range_self x, rfl⟩)
    refine ⟨m, ?_⟩
    change Q.atlas.chart T0 (BanachSpectrum.comap (h.pullback k T0 hT0).toBoundedRingHom x) ∈
      Set.range (Q.atlas.chart ((h.recognizedTargetChartCover k T0 hT0 W hW).index m))
    exact (congrArg (fun y => y ∈ Set.range
      (Q.atlas.chart ((h.recognizedTargetChartCover k T0 hT0 W hW).index m)))
        (h.chart_comm k T0 hT0 x)).mpr hm

/-- A spectrum point lies in a member exactly when its ambient image lies in
the corresponding target chart. -/
theorem mem_recognizedSourceDomainCover_iff (k : P.atlas.Index) (T0 : Q.atlas.Index)
    (hT0 : h.baseMap '' Set.range (P.atlas.chart k) ⊆ Set.range (Q.atlas.chart T0))
    (W : Q.atlas.RecognizedSubset)
    (hW : h.baseMap '' Set.range (P.atlas.chart k) ⊆ W.locus)
    (m : Fin (h.recognizedSourceDomainCover k T0 hT0 W hW).size)
    (x : BanachSpectrum (P.atlas.algebra k)) :
    x ∈ ((h.recognizedSourceDomainCover k T0 hT0 W hW).obj m).locus ↔
      h.baseMap (P.atlas.chart k x) ∈
        Set.range (Q.atlas.chart ((h.recognizedTargetChartCover k T0 hT0 W hW).index m)) := by
  change Q.atlas.chart T0 (BanachSpectrum.comap (h.pullback k T0 hT0).toBoundedRingHom x) ∈
      Set.range (Q.atlas.chart ((h.recognizedTargetChartCover k T0 hT0 W hW).index m)) ↔ _
  exact Iff.of_eq (congrArg (fun y => y ∈ Set.range
    (Q.atlas.chart ((h.recognizedTargetChartCover k T0 hT0 W hW).index m)))
      (h.chart_comm k T0 hT0 x))

end SourceCover

/-- On a source local domain mapping into a recognized target subset `W`,
the composite of the target-recognition pullback with the pair system of a
second map is the target-recognition pullback of the composite map. -/
theorem toFullRecognitionTarget_pullback_comp_fullRecognitionPairs
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (g' : StrongHom B.saturatedPresentation C.saturatedPresentation)
    (k : A.atlas.saturatedAtlas.Index) (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (Z : C.atlas.saturatedAtlas.RecognizedSubset)
    (hkW : g.toFullRecognitionTarget.baseMap '' Set.range (A.atlas.saturatedAtlas.chart k) ⊆
      Set.range (B.fullRecognitionPresentation.atlas.chart W))
    (hWZ : g'.baseMap '' Set.range W.chart ⊆ Set.range Z.chart)
    (hkZ : (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).toFullRecognitionTarget.baseMap ''
        Set.range (A.atlas.saturatedAtlas.chart k) ⊆
      Set.range (C.fullRecognitionPresentation.atlas.chart Z)) :
    (g.toFullRecognitionTarget.pullback k W hkW).comp (g'.fullRecognitionPairs.pullback W Z hWZ) =
      (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).toFullRecognitionTarget.pullback k Z hkZ := by
  classical
  have ha := A.atlas.saturatedAtlas_hasAllLocalDomains
  have hb := B.atlas.saturatedAtlas_hasAllLocalDomains
  have hc := C.atlas.saturatedAtlas_hasAllLocalDomains
  obtain ⟨T0, hT0⟩ := g.target_exists k
  have hSW : g.baseMap '' Set.range (A.atlas.saturatedAtlas.chart k) ⊆ W.locus :=
    hkW.trans W.range_chart.subset
  let cc := g.recognizedTargetChartCover k T0 hT0 W hSW
  let cov := g.recognizedSourceDomainCover k T0 hT0 W hSW
  let T : Fin cov.size → B.atlas.saturatedAtlas.Index := cc.index
  have hTW : ∀ m, Set.range (B.atlas.saturatedAtlas.chart (T m)) ⊆ W.locus :=
    cc.subset_recognized
  let D : Fin cov.size → Domain K (A.atlas.saturatedAtlas.algebra k) := cov.obj
  have hmem : ∀ (m : Fin cov.size) (x : BanachSpectrum (A.atlas.saturatedAtlas.algebra k)),
      x ∈ (D m).locus ↔
        g.baseMap (A.atlas.saturatedAtlas.chart k x) ∈
          Set.range (B.atlas.saturatedAtlas.chart (T m)) :=
    g.mem_recognizedSourceDomainCover_iff k T0 hT0 W hSW
  let L := (g.toFullRecognitionTarget.pullback k W hkW).comp
    (g'.fullRecognitionPairs.pullback W Z hWZ)
  let R := (g.saturatedComp g' ha hb).toFullRecognitionTarget.pullback k Z hkZ
  change L = R
  apply BoundedAlgHom.ext
  intro r
  apply cov.algebra_ext_of_restrict_eq
  intro m
  let U : LocalDomain A.atlas.saturatedAtlas := ⟨k, D m⟩
  obtain ⟨km, hkm⟩ := ha.exists_chart U
  have hkmk : Set.range (A.atlas.saturatedAtlas.chart km) ⊆
      Set.range (A.atlas.saturatedAtlas.chart k) := by
    rw [hkm]
    rintro _ ⟨x, _, rfl⟩
    exact Set.mem_range_self x
  have hDsub : (D m).locus ⊆ (A.atlas.saturatedAtlas.restrictionDomain km k hkmk).locus := by
    intro x hx
    change A.atlas.saturatedAtlas.chart k x ∈ Set.range (A.atlas.saturatedAtlas.chart km)
    rw [hkm]
    exact ⟨x, hx, rfl⟩
  let ι := Domain.inclusionOfSubset (D m)
    (A.atlas.saturatedAtlas.restrictionDomain km k hkmk) hDsub
  have himg : g.baseMap '' Set.range (A.atlas.saturatedAtlas.chart km) ⊆
      Set.range (B.atlas.saturatedAtlas.chart (T m)) := by
    rintro _ ⟨z, hz, rfl⟩
    have hz' : z ∈ U.locus := by
      rw [← hkm]
      exact hz
    obtain ⟨x, hx, rfl⟩ := hz'
    exact (hmem m x).1 hx
  have h1 : g.toFullRecognitionTarget.baseMap '' Set.range (A.atlas.saturatedAtlas.chart km) ⊆
      Set.range (B.fullRecognitionPresentation.atlas.chart W) :=
    (Set.image_mono hkmk).trans hkW
  have h2 := g'.toFullRecognitionTarget.recognized_admissible W Z hWZ (T m) (hTW m)
  have h3 : (g.saturatedComp g'.toFullRecognitionTarget ha hb).baseMap ''
      Set.range (A.atlas.saturatedAtlas.chart km) ⊆
        Set.range (C.fullRecognitionPresentation.atlas.chart Z) :=
    (Set.image_mono hkmk).trans hkZ
  have h3' : (g.saturatedComp g' ha hb).toFullRecognitionTarget.baseMap ''
      Set.range (A.atlas.saturatedAtlas.chart km) ⊆
        Set.range (C.fullRecognitionPresentation.atlas.chart Z) :=
    (Set.image_mono hkmk).trans hkZ
  have key : (A.atlas.saturatedAtlas.restriction km k hkmk).comp L =
      (A.atlas.saturatedAtlas.restriction km k hkmk).comp R := by
    exact (congrArg (fun q => BoundedAlgHom.comp q (g'.fullRecognitionPairs.pullback W Z hWZ))
        (g.toFullRecognitionTarget.restriction_comp_pullback km k W hkmk h1 hkW)).trans <|
      (congrArg (fun q => BoundedAlgHom.comp q (g'.fullRecognitionPairs.pullback W Z hWZ))
        (g.toFullRecognitionTarget_pullback km (T m) W himg (hTW m) h1)).trans <|
      (congrArg (fun q => BoundedAlgHom.comp (g.pullback km (T m) himg) q)
        (g'.toFullRecognitionTarget.originalRestriction_comp_recognizedSourceExtension
          W Z hWZ (T m) (hTW m))).trans <|
      (StrongHom.saturatedComp_pullback g g'.toFullRecognitionTarget ha hb km (T m) Z
        himg h2 h3).symm.trans <|
      (StrongHom.pullback_congr
        (StrongHom.saturatedComp_assoc g g' C.localDomainToFullRecognition ha hb hc).symm
        km Z h3 h3').trans
      ((g.saturatedComp g' ha hb).toFullRecognitionTarget.restriction_comp_pullback
        km k Z hkmk h3' hkZ).symm
  have hι := ι.comp_baseMap
  calc (D m).baseMap (L r)
      = (ι.restriction.comp (A.atlas.saturatedAtlas.restriction km k hkmk)) (L r) :=
        (congrArg (fun q => q (L r)) hι).symm
    _ = ι.restriction (((A.atlas.saturatedAtlas.restriction km k hkmk).comp L) r) := rfl
    _ = ι.restriction (((A.atlas.saturatedAtlas.restriction km k hkmk).comp R) r) := by
        rw [key]
    _ = (ι.restriction.comp (A.atlas.saturatedAtlas.restriction km k hkmk)) (R r) := rfl
    _ = (D m).baseMap (R r) := congrArg (fun q => q (R r)) hι

/-- Pair systems of strong maps of local-domain enlargements compose: the pair
system of the saturated composite on `V`, `Z` is the composite of the two pair
systems through any intermediate recognized subset `W`. -/
theorem fullRecognitionPairs_comp
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (g' : StrongHom B.saturatedPresentation C.saturatedPresentation)
    (V : A.atlas.saturatedAtlas.RecognizedSubset) (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (Z : C.atlas.saturatedAtlas.RecognizedSubset)
    (hVW : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart)
    (hWZ : g'.baseMap '' Set.range W.chart ⊆ Set.range Z.chart)
    (hVZ : (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap '' Set.range V.chart ⊆
      Set.range Z.chart) :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).fullRecognitionPairs.pullback V Z hVZ =
      (g.fullRecognitionPairs.pullback V W hVW).comp
        (g'.fullRecognitionPairs.pullback W Z hWZ) := by
  apply V.hom_ext
  intro k hk
  have hkW := g.toFullRecognitionTarget.recognized_admissible V W hVW k hk
  have hkZ := (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains).toFullRecognitionTarget.recognized_admissible
      V Z hVZ k hk
  exact ((g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).toFullRecognitionTarget.originalRestriction_comp_recognizedSourceExtension
        V Z hVZ k hk).trans <|
    (toFullRecognitionTarget_pullback_comp_fullRecognitionPairs g g' k W Z hkW hWZ hkZ).symm.trans
    (congrArg (fun q => BoundedAlgHom.comp q (g'.fullRecognitionPairs.pullback W Z hWZ))
      (g.toFullRecognitionTarget.originalRestriction_comp_recognizedSourceExtension
        V W hVW k hk).symm)

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic
