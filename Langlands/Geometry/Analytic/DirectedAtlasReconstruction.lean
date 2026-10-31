import Langlands.Geometry.Analytic.AtlasSpectrumColimit
import Langlands.Geometry.Analytic.DirectedAtlasMaps

/-! # Full strong maps from compatible bounded local choices -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation

open CategoryTheory CategoryTheory.Limits Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Bounded chart maps with arbitrary target choices. Compatibility is required
in one common original upper chart for each source containment.
Neither an ambient map nor a monotone target choice is supplied. -/
structure LocalChartMapData (A B : AffinoidAtlasPresentation.{u, v, w} K) where
  indexMap : A.atlas.Index → B.atlas.Index
  pullback : ∀ i, BoundedAlgHom K (B.atlas.algebra (indexMap i)) (A.atlas.algebra i)
  restriction_comm : ∀ i i'
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i')),
    ∃ (q : B.atlas.Index)
      (hs : Set.range (B.atlas.chart (indexMap i)) ⊆ Set.range (B.atlas.chart q))
      (hs' : Set.range (B.atlas.chart (indexMap i')) ⊆ Set.range (B.atlas.chart q)),
      (A.atlas.restriction i i' hi).comp
          ((pullback i').comp (B.atlas.restriction (indexMap i') q hs')) =
        (pullback i).comp (B.atlas.restriction (indexMap i) q hs)

namespace LocalChartMapData

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- The original bounded map followed by restriction from an upper target. -/
def pullbackToUpper (d : LocalChartMapData A B) (i : A.atlas.Index) (q : B.atlas.Index)
    (hq : Set.range (B.atlas.chart (d.indexMap i)) ⊆ Set.range (B.atlas.chart q)) :
    BoundedAlgHom K (B.atlas.algebra q) (A.atlas.algebra i) :=
  (d.pullback i).comp (B.atlas.restriction (d.indexMap i) q hq)

/-- The actual local spectrum maps form a cocone without a target chart functor. -/
def chartCocone (d : LocalChartMapData A B) :
    Cocone (A.atlas.chartSpectrumDiagram ⋙ TopCat.uliftFunctor.{v}) where
  pt := B.atlas.chartSpectrumCocone.pt
  ι :=
    { app := fun i =>
        TopCat.uliftFunctor.{v}.map
          (TopCat.ofHom (BanachSpectrum.comapContinuous (d.pullback i.index).toBoundedRingHom)) ≫
            B.atlas.chartSpectrumCocone.ι.app ⟨d.indexMap i.index⟩
      naturality := by
        intro i i' h
        apply TopCat.ext
        intro x
        apply ULift.ext
        obtain ⟨q, hs, hs', hc⟩ :=
          d.restriction_comm i.index i'.index (A.atlas.chartSubsetOfHom h)
        have hc' := congrArg (fun φ : BoundedAlgHom K (B.atlas.algebra q)
            (A.atlas.algebra i.index) =>
          B.atlas.chart q (BanachSpectrum.comap φ.toBoundedRingHom x.down)) hc
        change B.atlas.chart q
          (BanachSpectrum.comap (B.atlas.restriction (d.indexMap i'.index) q hs').toBoundedRingHom
            (BanachSpectrum.comap (d.pullback i'.index).toBoundedRingHom
              (BanachSpectrum.comap
                (A.atlas.restriction i.index i'.index
                  (A.atlas.chartSubsetOfHom h)).toBoundedRingHom x.down))) =
          B.atlas.chart q
            (BanachSpectrum.comap (B.atlas.restriction (d.indexMap i.index) q hs).toBoundedRingHom
              (BanachSpectrum.comap (d.pullback i.index).toBoundedRingHom x.down)) at hc'
        rw [B.atlas.restriction_chart, B.atlas.restriction_chart] at hc'
        exact hc' }

/-- Descend the genuine local spectrum maps through the spectrum-chart colimit. -/
def liftedBaseMap (d : LocalChartMapData A B) :
    A.atlas.chartSpectrumCocone.pt ⟶ B.atlas.chartSpectrumCocone.pt :=
  A.atlas.chartSpectrumCoconeIsColimit.desc d.chartCocone

/-- The ambient continuous map is constructed, with the universe lifts removed. -/
def baseMap (d : LocalChartMapData A B) : C(A.space, B.space) :=
  ⟨fun x => (d.liftedBaseMap (ULift.up x)).down,
    continuous_uliftDown.comp
      (d.liftedBaseMap.hom.continuous.comp continuous_uliftUp)⟩

/-- The constructed ambient map has exactly the supplied bounded chart formula. -/
theorem chart_comm (d : LocalChartMapData A B) (i : A.atlas.Index)
    (x : BanachSpectrum (A.atlas.algebra i)) :
    B.atlas.chart (d.indexMap i) (BanachSpectrum.comap (d.pullback i).toBoundedRingHom x) =
      d.baseMap (A.atlas.chart i x) :=
  (congrArg ULift.down
    (A.atlas.chartSpectrumCocone_desc_chart d.chartCocone ⟨i⟩ x)).symm

/-- Each original source chart maps into its independently selected target chart. -/
theorem image_chart_subset (d : LocalChartMapData A B) (i : A.atlas.Index) :
    d.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart (d.indexMap i)) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨BanachSpectrum.comap (d.pullback i).toBoundedRingHom x, d.chart_comm i x⟩

/-- The actual chart formulas determine the ambient map uniquely. -/
theorem baseMap_unique (d : LocalChartMapData A B) (g : C(A.space, B.space))
    (hg : ∀ i (x : BanachSpectrum (A.atlas.algebra i)),
      B.atlas.chart (d.indexMap i) (BanachSpectrum.comap (d.pullback i).toBoundedRingHom x) =
        g (A.atlas.chart i x)) :
    d.baseMap = g := by
  have h : d.liftedBaseMap = TopCat.uliftFunctor.{u}.map (TopCat.ofHom g) := by
    apply A.atlas.chartSpectrumCocone_hom_ext
    intro i x
    exact (A.atlas.chartSpectrumCocone_desc_chart d.chartCocone i x).trans
      (congrArg ULift.up (hg i.index x))
  apply ContinuousMap.ext
  intro x
  exact congrArg (fun f : A.atlas.chartSpectrumCocone.pt ⟶
    B.atlas.chartSpectrumCocone.pt => (f (ULift.up x)).down) h

/-- The single chosen bounded map defines a genuine chosen arrow on its
source chart domain, with a constant target index. -/
def localHom (d : LocalChartMapData A B) (i : A.atlas.Index) :
    A.chartPresentation i ⟶ B where
  baseMap :=
    (show C(_, _) from
      ⟨B.atlas.chart (d.indexMap i), (B.atlas.isEmbedding_chart _).continuous⟩).comp
      ((BanachSpectrum.comapContinuous (d.pullback i).toBoundedRingHom).comp
        (show C(_, _) from ⟨(A.atlas.isEmbedding_chart i).toHomeomorph.symm,
          (A.atlas.isEmbedding_chart i).toHomeomorph.symm.continuous⟩))
  indexMap _ := d.indexMap i
  index_mono _ _ _ := Subset.rfl
  pullback c := (A.atlas.restriction c.val i c.property).comp (d.pullback i)
  chart_comm c x := by
    have hc :
        (A.atlas.isEmbedding_chart i).toHomeomorph.symm
            ((A.chartPresentation i).atlas.chart c x) =
          BanachSpectrum.comap (A.atlas.restriction c.val i c.property).toBoundedRingHom x := by
      change (A.atlas.isEmbedding_chart i).toHomeomorph.symm
          (⟨A.atlas.chart c.val x, c.property ⟨x, rfl⟩⟩ : Set.range (A.atlas.chart i)) = _
      apply (A.atlas.isEmbedding_chart i).toHomeomorph.injective
      rw [Homeomorph.apply_symm_apply]
      apply Subtype.ext
      exact (A.atlas.restriction_chart c.val i c.property x).symm
    change B.atlas.chart (d.indexMap i)
      (BanachSpectrum.comap (d.pullback i).toBoundedRingHom
        (BanachSpectrum.comap (A.atlas.restriction c.val i c.property).toBoundedRingHom x)) =
      B.atlas.chart (d.indexMap i)
        (BanachSpectrum.comap (d.pullback i).toBoundedRingHom
          ((A.atlas.isEmbedding_chart i).toHomeomorph.symm
            ((A.chartPresentation i).atlas.chart c x)))
    rw [hc]
  restriction_comm c c' hi := by
    change (A.atlas.restriction c.val c'.val _).comp
        ((A.atlas.restriction c'.val i c'.property).comp (d.pullback i)) =
      ((A.atlas.restriction c.val i c.property).comp (d.pullback i)).comp
        (B.atlas.restriction (d.indexMap i) (d.indexMap i) _)
    rw [B.atlas.restriction_id, BoundedAlgHom.comp_id,
      ← BoundedAlgHom.comp_assoc, ← A.atlas.restriction_comp]

/-- The chart-domain arrow retains the supplied bounded pullback at its top. -/
theorem localHom_pullback_top (d : LocalChartMapData A B) (i : A.atlas.Index) :
    (d.localHom i).pullback (A.chartTopIndex i) = d.pullback i := by
  change (A.atlas.restriction i i Subset.rfl).comp (d.pullback i) = _
  rw [A.atlas.restriction_id, BoundedAlgHom.id_comp]

/-- The local chosen map is the restriction of the constructed ambient map. -/
theorem localHom_baseMap (d : LocalChartMapData A B) (i : A.atlas.Index) :
    (d.localHom i).baseMap = d.baseMap.comp (A.chartInclusion i).baseMap := by
  apply ContinuousMap.ext
  rintro ⟨_, x, rfl⟩
  have h := (d.localHom i).chart_comm (A.chartTopIndex i) x
  rw [d.localHom_pullback_top] at h
  exact h.symm.trans (d.chart_comm i x)

/-- Translate admissibility into the actual source chart-domain presentation. -/
theorem localHom_admissible (d : LocalChartMapData A B)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : d.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    (d.localHom i).baseMap ''
        Set.range ((A.chartPresentation i).atlas.chart (A.chartTopIndex i)) ⊆
      Set.range (B.atlas.chart j) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  rw [d.localHom_baseMap]
  exact h ⟨_, ⟨x, rfl⟩, rfl⟩

/-- Use the published directed factorization on the actual source chart domain. -/
def fullPullback (d : LocalChartMapData A B) (hd : B.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : d.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    BoundedAlgHom K (B.atlas.algebra j) (A.atlas.algebra i) :=
  (d.localHom i).directedPullback hd (A.chartTopIndex i) j (d.localHom_admissible i j h)

/-- Every upper-chart equation is an equality of actual bounded maps. -/
theorem fullPullback_comp_restriction (d : LocalChartMapData A B)
    (hd : B.atlas.HasDirectedCharts) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : d.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (q : B.atlas.Index)
    (hs : Set.range (B.atlas.chart (d.indexMap i)) ⊆ Set.range (B.atlas.chart q))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart q)) :
    (d.fullPullback hd i j h).comp (B.atlas.restriction j q hj) =
      d.pullbackToUpper i q hs := by
  have hq := (d.localHom i).directedPullback_comp_restriction hd
    (A.chartTopIndex i) j (d.localHom_admissible i j h) q hs hj
  change (d.fullPullback hd i j h).comp (B.atlas.restriction j q hj) =
    ((d.localHom i).pullback (A.chartTopIndex i)).comp
      (B.atlas.restriction (d.indexMap i) q hs) at hq
  rw [d.localHom_pullback_top] at hq
  exact hq

/-- The bounded factorization has the constructed ambient chart square. -/
theorem fullPullback_chart (d : LocalChartMapData A B) (hd : B.atlas.HasDirectedCharts)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (h : d.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (x : BanachSpectrum (A.atlas.algebra i)) :
    B.atlas.chart j (BanachSpectrum.comap (d.fullPullback hd i j h).toBoundedRingHom x) =
      d.baseMap (A.atlas.chart i x) := by
  have hc := (d.localHom i).directedPullback_chart hd (A.chartTopIndex i) j
    (d.localHom_admissible i j h) x
  rw [d.localHom_baseMap] at hc
  exact hc

/-- Upper-chart restriction preserves the actual selected bounded map. -/
theorem pullbackToUpper_comp (d : LocalChartMapData A B)
    (i : A.atlas.Index) (q r : B.atlas.Index)
    (hq : Set.range (B.atlas.chart (d.indexMap i)) ⊆ Set.range (B.atlas.chart q))
    (hqr : Set.range (B.atlas.chart q) ⊆ Set.range (B.atlas.chart r)) :
    (d.pullbackToUpper i q hq).comp (B.atlas.restriction q r hqr) =
      d.pullbackToUpper i r (hq.trans hqr) := by
  dsimp only [pullbackToUpper]
  rw [BoundedAlgHom.comp_assoc, ← B.atlas.restriction_comp]

/-- Compatibility in one original upper chart implies compatibility in every
original common upper chart, by bounded domain uniqueness. -/
theorem restriction_comm_upper (d : LocalChartMapData A B)
    (hd : B.atlas.HasDirectedCharts) (i i' : A.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (q : B.atlas.Index)
    (hs : Set.range (B.atlas.chart (d.indexMap i)) ⊆ Set.range (B.atlas.chart q))
    (hs' : Set.range (B.atlas.chart (d.indexMap i')) ⊆ Set.range (B.atlas.chart q)) :
    (A.atlas.restriction i i' hi).comp (d.pullbackToUpper i' q hs') =
      d.pullbackToUpper i q hs := by
  obtain ⟨q₀, hs₀, hs₀', hc⟩ := d.restriction_comm i i' hi
  obtain ⟨r, h₀r, hqr⟩ := hd q₀ q
  apply B.atlas.restriction_hom_ext q r hqr (A.atlas.algebra i)
  calc
    ((A.atlas.restriction i i' hi).comp (d.pullbackToUpper i' q hs')).comp
        (B.atlas.restriction q r hqr) =
        (A.atlas.restriction i i' hi).comp
          (d.pullbackToUpper i' r (hs'.trans hqr)) := by
      rw [BoundedAlgHom.comp_assoc, d.pullbackToUpper_comp]
    _ = ((A.atlas.restriction i i' hi).comp (d.pullbackToUpper i' q₀ hs₀')).comp
        (B.atlas.restriction q₀ r h₀r) := by
      rw [BoundedAlgHom.comp_assoc, d.pullbackToUpper_comp]
    _ = (d.pullbackToUpper i q₀ hs₀).comp (B.atlas.restriction q₀ r h₀r) :=
      congrArg (fun φ => φ.comp (B.atlas.restriction q₀ r h₀r)) hc
    _ = (d.pullbackToUpper i q hs).comp (B.atlas.restriction q r hqr) := by
      rw [d.pullbackToUpper_comp, d.pullbackToUpper_comp]

/-- The constructed pullbacks are compatible with both source and target restrictions. -/
theorem fullPullback_naturality (d : LocalChartMapData A B)
    (hd : B.atlas.HasDirectedCharts) (i i' : A.atlas.Index) (j j' : B.atlas.Index)
    (hi : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hj : Set.range (B.atlas.chart j) ⊆ Set.range (B.atlas.chart j'))
    (h : d.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (h' : d.baseMap '' Set.range (A.atlas.chart i') ⊆ Set.range (B.atlas.chart j')) :
    (A.atlas.restriction i i' hi).comp (d.fullPullback hd i' j' h') =
      (d.fullPullback hd i j h).comp (B.atlas.restriction j j' hj) := by
  obtain ⟨q₀, hs₀, hs₀'⟩ := hd (d.indexMap i) (d.indexMap i')
  obtain ⟨q, h₀q, hj'q⟩ := hd q₀ j'
  have hs := hs₀.trans h₀q
  have hs' := hs₀'.trans h₀q
  have hjq := hj.trans hj'q
  apply B.atlas.restriction_hom_ext j' q hj'q (A.atlas.algebra i)
  calc
    ((A.atlas.restriction i i' hi).comp (d.fullPullback hd i' j' h')).comp
        (B.atlas.restriction j' q hj'q) =
        (A.atlas.restriction i i' hi).comp (d.pullbackToUpper i' q hs') := by
      rw [BoundedAlgHom.comp_assoc, d.fullPullback_comp_restriction]
    _ = d.pullbackToUpper i q hs := d.restriction_comm_upper hd i i' hi q hs hs'
    _ = (d.fullPullback hd i j h).comp (B.atlas.restriction j q hjq) :=
      (d.fullPullback_comp_restriction hd i j h q hs hjq).symm
    _ = ((d.fullPullback hd i j h).comp (B.atlas.restriction j j' hj)).comp
        (B.atlas.restriction j' q hj'q) := by
      rw [BoundedAlgHom.comp_assoc, ← B.atlas.restriction_comp]

/-- Recovery is equality of bounded maps, even for nonreduced chart algebras. -/
theorem fullPullback_selected (d : LocalChartMapData A B)
    (hd : B.atlas.HasDirectedCharts) (i : A.atlas.Index) :
    d.fullPullback hd i (d.indexMap i) (d.image_chart_subset i) = d.pullback i :=
  ((d.localHom i).directedPullback_selected hd (A.chartTopIndex i)).trans
    (d.localHom_pullback_top i)

/-- Construct the full strong morphism from compatible local algebra data. -/
def toStrongHom (d : LocalChartMapData A B) (hd : B.atlas.HasDirectedCharts) :
    StrongHom A B where
  baseMap := d.baseMap
  target_exists i := ⟨d.indexMap i, d.image_chart_subset i⟩
  pullback := d.fullPullback hd
  chart_comm := d.fullPullback_chart hd
  restriction_comm := d.fullPullback_naturality hd

@[simp]
theorem toStrongHom_baseMap (d : LocalChartMapData A B) (hd : B.atlas.HasDirectedCharts) :
    (d.toStrongHom hd).baseMap = d.baseMap := rfl

/-- The complete strong map retains exactly the independently supplied local maps. -/
theorem toStrongHom_pullback_selected (d : LocalChartMapData A B)
    (hd : B.atlas.HasDirectedCharts) (i : A.atlas.Index) :
    (d.toStrongHom hd).pullback i (d.indexMap i) (d.image_chart_subset i) = d.pullback i :=
  d.fullPullback_selected hd i

/-- Realization asks only for equality with each selected bounded map.
The ambient map and all other admissible bounded pullbacks are outputs. -/
def RealizedBy (d : LocalChartMapData A B) (f : StrongHom A B) : Prop :=
  ∀ i, ∃ h : f.baseMap '' Set.range (A.atlas.chart i) ⊆
    Set.range (B.atlas.chart (d.indexMap i)), f.pullback i (d.indexMap i) h = d.pullback i

theorem toStrongHom_realizedBy (d : LocalChartMapData A B) (hd : B.atlas.HasDirectedCharts) :
    d.RealizedBy (d.toStrongHom hd) :=
  fun i => ⟨d.image_chart_subset i, d.toStrongHom_pullback_selected hd i⟩

/-- Selected algebraic realization forces the actual ambient map. -/
theorem RealizedBy.baseMap_eq {d : LocalChartMapData A B} {f : StrongHom A B}
    (hf : d.RealizedBy f) : f.baseMap = d.baseMap := by
  apply Eq.symm
  apply d.baseMap_unique
  intro i x
  obtain ⟨h, hp⟩ := hf i
  rw [← hp]
  exact f.chart_comm i (d.indexMap i) h x

/-- Algebraic realization uniquely determines the entire strong map.
Point-map equality alone is not used to identify bounded algebra maps. -/
theorem RealizedBy.eq_toStrongHom {d : LocalChartMapData A B} {f : StrongHom A B}
    (hf : d.RealizedBy f) (hd : B.atlas.HasDirectedCharts) :
    f = d.toStrongHom hd := by
  have hb := hf.baseMap_eq
  rcases f with ⟨fb, ft, fp, fc, fr⟩
  dsimp only [StrongHom.baseMap] at hb
  subst fb
  refine StrongHom.ext (f := ⟨d.baseMap, ft, fp, fc, fr⟩) (g := d.toStrongHom hd) rfl ?_
  apply heq_of_eq
  funext i j h
  obtain ⟨q, hs, hj⟩ := hd (d.indexMap i) j
  apply B.atlas.restriction_hom_ext j q hj (A.atlas.algebra i)
  obtain ⟨hsel, hp⟩ := hf i
  change fp i (d.indexMap i) hsel = d.pullback i at hp
  have hq := (d.image_chart_subset i).trans hs
  have h₁ := fr i i j q Subset.rfl hj h hq
  have h₂ := fr i i (d.indexMap i) q Subset.rfl hs hsel hq
  simp only [A.atlas.restriction_id, BoundedAlgHom.id_comp] at h₁ h₂
  change (fp i j h).comp (B.atlas.restriction j q hj) =
    (d.fullPullback hd i j h).comp (B.atlas.restriction j q hj)
  calc
    (fp i j h).comp (B.atlas.restriction j q hj) = fp i q hq := h₁.symm
    _ = (fp i (d.indexMap i) hsel).comp
        (B.atlas.restriction (d.indexMap i) q hs) := h₂
    _ = d.pullbackToUpper i q hs := by rw [hp]; rfl
    _ = (d.fullPullback hd i j h).comp (B.atlas.restriction j q hj) :=
      (d.fullPullback_comp_restriction hd i j h q hs hj).symm

/-- Existence and uniqueness of the full strong morphism require no ambient-map
or monotone-chart output among the local inputs. -/
theorem existsUnique_strongHom (d : LocalChartMapData A B) (hd : B.atlas.HasDirectedCharts) :
    ∃! f : StrongHom A B, d.RealizedBy f :=
  ⟨d.toStrongHom hd, d.toStrongHom_realizedBy hd, fun _ hf => hf.eq_toStrongHom hd⟩

end LocalChartMapData

namespace StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Extract local bounded data with any admissible target choices.
Directedness supplies the common upper charts for their compatibility. -/
def toLocalChartMapData (f : StrongHom A B) (hd : B.atlas.HasDirectedCharts)
    (σ : A.atlas.Index → B.atlas.Index)
    (hσ : ∀ i, f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart (σ i))) :
    LocalChartMapData A B where
  indexMap := σ
  pullback i := f.pullback i (σ i) (hσ i)
  restriction_comm i i' hi := by
    obtain ⟨q, hs, hs'⟩ := hd (σ i) (σ i')
    refine ⟨q, hs, hs', ?_⟩
    rw [← f.pullback_comp_restriction i' (σ i') q hs' (hσ i') ((hσ i').trans hs'),
      ← f.pullback_comp_restriction i (σ i) q hs (hσ i) ((hσ i).trans hs)]
    simpa only [B.atlas.restriction_id, BoundedAlgHom.comp_id] using
      f.restriction_comm i i' q q hi Subset.rfl ((hσ i).trans hs) ((hσ i').trans hs')

theorem toLocalChartMapData_realizedBy (f : StrongHom A B) (hd : B.atlas.HasDirectedCharts)
    (σ : A.atlas.Index → B.atlas.Index)
    (hσ : ∀ i, f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart (σ i))) :
    (f.toLocalChartMapData hd σ hσ).RealizedBy f :=
  fun i => ⟨hσ i, rfl⟩

/-- Reconstructing any admissible selection recovers every bounded pullback. -/
theorem toLocalChartMapData_toStrongHom (f : StrongHom A B)
    (hd : B.atlas.HasDirectedCharts) (σ : A.atlas.Index → B.atlas.Index)
    (hσ : ∀ i, f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart (σ i))) :
    (f.toLocalChartMapData hd σ hσ).toStrongHom hd = f :=
  ((f.toLocalChartMapData_realizedBy hd σ hσ).eq_toStrongHom hd).symm

theorem toLocalChartMapData_baseMap (f : StrongHom A B)
    (hd : B.atlas.HasDirectedCharts) (σ : A.atlas.Index → B.atlas.Index)
    (hσ : ∀ i, f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart (σ i))) :
    (f.toLocalChartMapData hd σ hσ).baseMap = f.baseMap :=
  (f.toLocalChartMapData_realizedBy hd σ hσ).baseMap_eq.symm

end StrongHom

namespace Hom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- A chosen arrow supplies local data without retaining its ambient map
or requiring its monotonicity as part of the new input. -/
def toLocalChartMapData (f : A ⟶ B) : LocalChartMapData A B where
  indexMap := f.indexMap
  pullback := f.pullback
  restriction_comm i i' hi := by
    refine ⟨f.indexMap i', f.index_mono i i' hi, Subset.rfl, ?_⟩
    rw [B.atlas.restriction_id, BoundedAlgHom.comp_id]
    exact f.restriction_comm i i' hi

theorem toLocalChartMapData_baseMap (f : A ⟶ B) :
    f.toLocalChartMapData.baseMap = f.baseMap :=
  f.toLocalChartMapData.baseMap_unique f.baseMap f.chart_comm

/-- Local reconstruction agrees with the existing directed extension of
a chosen arrow as an equality of complete strong morphisms. -/
theorem toLocalChartMapData_toStrongHom (f : A ⟶ B) (hd : B.atlas.HasDirectedCharts) :
    f.toLocalChartMapData.toStrongHom hd = StrongHom.ofDirected f hd := by
  apply Eq.symm
  apply LocalChartMapData.RealizedBy.eq_toStrongHom
  intro i
  exact ⟨f.image_chart_subset i, StrongHom.ofDirected_pullback_selected f hd i⟩

end Hom

end Langlands.Analytic.AffinoidAtlasPresentation
