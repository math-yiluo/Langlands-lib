import Langlands.Geometry.Analytic.GroundFieldExtensionAtlas
import Langlands.Geometry.Analytic.CompatibleStrongMaps
import Langlands.Geometry.Analytic.StrongAtlasComposition

/-! # Ground field extension of compatible strong atlas maps -/

noncomputable section

universe u v w u'

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open Set Topology PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension
open IndexedAffinoidAtlas.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- The map from a scalar-extended source chart into the actual glued target,
using any original admissible target chart. -/
def chartMap (f : StrongHom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (s : BanachSpectrum (chartAlgebra K L A.atlas i)) :
    (chartSystem K L B.atlas).Space :=
  (chartSystem K L B.atlas).chart j
    (BanachSpectrum.comap (map K L (f.pullback i j h)).toBoundedRingHom s)

theorem projection_chartMap (f : StrongHom A B) (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (s : BanachSpectrum (chartAlgebra K L A.atlas i)) :
    projection K L B.atlas (chartMap K L f i j h s) =
      f.baseMap (A.atlas.chart i (spectrumProjection K L (A.atlas.algebra i) s)) := by
  rw [chartMap, projection_chart, spectrumProjection_naturality, f.chart_comm]

/-- Local compatibility on original inverse-image domains makes the extended
chart map independent of the admissible target chart. -/
theorem chartMap_independent (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks)
    (i : A.atlas.Index) (j k : B.atlas.Index)
    (hj : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (hk : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart k))
    (s : BanachSpectrum (chartAlgebra K L A.atlas i)) :
    chartMap K L f i j hj s = chartMap K L f i k hk s := by
  let C := chartSystem K L B.atlas
  let x := f.baseMap (A.atlas.chart i (spectrumProjection K L (A.atlas.algebra i) s))
  obtain ⟨m, hm, hxm⟩ := IndexedAffinoidAtlas.exists_chart_inter (a := B.atlas)
    (hj ⟨_, ⟨_, rfl⟩, rfl⟩) (hk ⟨_, ⟨_, rfl⟩, rfl⟩)
  let hmj := hm.trans inter_subset_left
  let hmk := hm.trans inter_subset_right
  let D := B.atlas.restrictionDomain m j hmj
  let Q := Domain.pullback (f.pullback i j hj) D
  have hsQ : spectrumProjection K L (A.atlas.algebra i) s ∈ Q.locus := by
    change B.atlas.chart j (BanachSpectrum.comap
      (f.pullback i j hj).toBoundedRingHom (spectrumProjection K L (A.atlas.algebra i) s)) ∈
        range (B.atlas.chart m)
    rw [f.chart_comm]
    exact hxm
  have hQ := domainPreservation.{u, u'} K L (A.atlas.algebra i) Q.algebra Q.baseMap Q.locus Q.represents
  have hsQ' : s ∈ range (BanachSpectrum.comap (map K L Q.baseMap).toBoundedRingHom) := by
    rw [hQ.2.1]
    exact hsQ
  obtain ⟨t, ht⟩ := hsQ'
  let α : BoundedAlgHom K (B.atlas.algebra m) Q.algebra :=
    Domain.pullbackMap (f.pullback i j hj) D
  let r : BanachSpectrum (chartAlgebra K L B.atlas m) :=
    BanachSpectrum.comap (map K L α).toBoundedRingHom t
  have hjr : C.pull hmj r =
      BanachSpectrum.comap (map K L (f.pullback i j hj)).toBoundedRingHom s := by
    rw [← ht]
    have hbase : α.comp (B.atlas.restriction m j hmj) =
        Q.baseMap.comp (f.pullback i j hj) :=
      Domain.pullbackMap_comp_baseMap (f.pullback i j hj) D
    have heq : (map K L α).comp (map K L (B.atlas.restriction m j hmj)) =
        (map K L Q.baseMap).comp (map K L (f.pullback i j hj)) := by
      simpa only [map_comp] using congrArg (map K L) hbase
    exact congrArg (fun φ : BoundedAlgHom L (chartAlgebra K L B.atlas j)
      (PresentedAffinoidAlgebra.GroundFieldExtension.algebra K L Q.algebra) =>
        BanachSpectrum.comap φ.toBoundedRingHom t) heq
  have hkr : C.pull hmk r =
      BanachSpectrum.comap (map K L (f.pullback i k hk)).toBoundedRingHom s := by
    rw [← ht]
    have heq : (map K L α).comp (map K L (B.atlas.restriction m k hmk)) =
        (map K L Q.baseMap).comp (map K L (f.pullback i k hk)) := by
      rw [← map_comp, ← map_comp]
      exact congrArg (map K L) (hf i j k hj hk m hmj hmk).symm
    exact congrArg (fun φ : BoundedAlgHom L (chartAlgebra K L B.atlas k)
      (PresentedAffinoidAlgebra.GroundFieldExtension.algebra K L Q.algebra) =>
        BanachSpectrum.comap φ.toBoundedRingHom t) heq
  change C.chart j _ = C.chart k _
  rw [← hjr, ← hkr, C.chart_pull, C.chart_pull]

/-- Source restriction compatibility is preserved by scalar extension. -/
theorem chartMap_pull (f : StrongHom A B) (i i' : A.atlas.Index) (j : B.atlas.Index)
    (hi : range (A.atlas.chart i) ⊆ range (A.atlas.chart i'))
    (hj : f.baseMap '' range (A.atlas.chart i') ⊆ range (B.atlas.chart j))
    (s : BanachSpectrum (chartAlgebra K L A.atlas i)) :
    chartMap K L f i' j hj ((chartSystem K L A.atlas).pull hi s) =
      chartMap K L f i j ((image_mono hi).trans hj) s := by
  unfold chartMap
  congr 1
  have heq : (map K L (A.atlas.restriction i i' hi)).comp
      (map K L (f.pullback i' j hj)) =
        map K L (f.pullback i j ((image_mono hi).trans hj)) := by
    rw [← map_comp, f.restriction_comp_pullback]
  exact congrArg (fun φ : BoundedAlgHom L (chartAlgebra K L B.atlas j)
    (chartAlgebra K L A.atlas i) => BanachSpectrum.comap φ.toBoundedRingHom s) heq

/-- A choice of admissible target chart used to define the quotient map. -/
def chosenChartMap (f : StrongHom A B) (i : A.atlas.Index) :
    BanachSpectrum (chartAlgebra K L A.atlas i) →
      (chartSystem K L B.atlas).Space :=
  chartMap K L f i (f.target_exists i).choose (f.target_exists i).choose_spec

theorem chosenChartMap_eq (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (hj : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (s : BanachSpectrum (chartAlgebra K L A.atlas i)) :
    chosenChartMap K L f i s = chartMap K L f i j hj s :=
  chartMap_independent K L f hf i _ j _ hj s

theorem chosenChartMap_pull (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks)
    (i i' : A.atlas.Index)
    (hi : range (A.atlas.chart i) ⊆ range (A.atlas.chart i'))
    (s : BanachSpectrum (chartAlgebra K L A.atlas i)) :
    chosenChartMap K L f i' ((chartSystem K L A.atlas).pull hi s) =
      chosenChartMap K L f i s := by
  obtain ⟨j, hj⟩ := f.target_exists i'
  rw [chosenChartMap_eq K L f hf i' j hj,
    chosenChartMap_eq K L f hf i j ((image_mono hi).trans hj), chartMap_pull]

/-- The continuous map between actual scalar-extension quotients is obtained
by descent of scalar-extended compatible chart maps. -/
def pointMap (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks) :
    (chartSystem K L A.atlas).Space → (chartSystem K L B.atlas).Space :=
  Quotient.lift (fun z => chosenChartMap K L f z.1 z.2) (by
    rintro ⟨i, s⟩ ⟨j, t⟩ ⟨m, hmi, hmj, r, hrs, hrt⟩
    change chosenChartMap K L f i s = chosenChartMap K L f j t
    change (chartSystem K L A.atlas).pull hmi r = s at hrs
    change (chartSystem K L A.atlas).pull hmj r = t at hrt
    rw [← hrs, ← hrt, chosenChartMap_pull K L f hf,
      chosenChartMap_pull K L f hf])

theorem pointMap_chart (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks)
    (i : A.atlas.Index) (j : B.atlas.Index)
    (hj : f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j))
    (s : BanachSpectrum (chartAlgebra K L A.atlas i)) :
    pointMap K L f hf ((chartSystem K L A.atlas).chart i s) =
      chartMap K L f i j hj s :=
  chosenChartMap_eq K L f hf i j hj s

theorem continuous_pointMap (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks) :
    Continuous (pointMap K L f hf) := by
  apply Continuous.quotient_lift
  refine continuous_sigma fun i => ?_
  change Continuous (chosenChartMap K L f i)
  unfold chosenChartMap chartMap
  exact ((chartSystem K L B.atlas).continuous_chart _).comp
    (BanachSpectrum.comapContinuous _).continuous

/-- Naturality of the continuous projection for the glued map. -/
theorem projection_pointMap (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks)
    (z : (chartSystem K L A.atlas).Space) :
    projection K L B.atlas (pointMap K L f hf z) =
      f.baseMap (projection K L A.atlas z) := by
  obtain ⟨i, s, rfl⟩ := (chartSystem K L A.atlas).exists_chart z
  obtain ⟨j, hj⟩ := f.target_exists i
  rw [pointMap_chart K L f hf i j hj, projection_chartMap, projection_chart]

/-- An admissible pair after extension is exactly an original admissible
pair; surjectivity prevents losing any original base points. -/
theorem admissible_iff (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks)
    (i : A.atlas.Index) (j : B.atlas.Index) :
    pointMap K L f hf '' range ((chartSystem K L A.atlas).chart i) ⊆
      range ((chartSystem K L B.atlas).chart j) ↔
        f.baseMap '' range (A.atlas.chart i) ⊆ range (B.atlas.chart j) := by
  constructor
  · intro h
    rintro _ ⟨x, hx, rfl⟩
    have hx' : x ∈ projection K L A.atlas ''
        range ((chartSystem K L A.atlas).chart i) := by
      rw [projection_image_chart K L A.atlas]
      exact hx
    obtain ⟨z, hz, hzx⟩ := hx'
    have hp := h ⟨z, hz, rfl⟩
    rw [range_chart] at hp
    change projection K L B.atlas (pointMap K L f hf z) ∈
      range (B.atlas.chart j) at hp
    rwa [projection_pointMap, hzx] at hp
  · intro h
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    rw [pointMap_chart K L f hf i j h]
    exact ⟨_, rfl⟩

/-- The scalar-extended full family of admissible bounded pullbacks. -/
def strongMap (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks) :
    StrongHom (presentation K L A.atlas)
      (presentation K L B.atlas) where
  baseMap := ⟨pointMap K L f hf, continuous_pointMap K L f hf⟩
  target_exists i := by
    obtain ⟨j, hj⟩ := f.target_exists i
    exact ⟨j, (admissible_iff K L f hf i j).2 hj⟩
  pullback i j h := map K L (f.pullback i j ((admissible_iff K L f hf i j).1 h))
  chart_comm i j h s :=
    (pointMap_chart K L f hf i j ((admissible_iff K L f hf i j).1 h) s).symm
  restriction_comm i i' j j' hi hj h h' := by
    have hi' := (range_chart_subset_iff K L A.atlas i i').1 hi
    have hj' := (range_chart_subset_iff K L B.atlas j j').1 hj
    have h₁ := (admissible_iff K L f hf i j).1 h
    have h₂ := (admissible_iff K L f hf i' j').1 h'
    change (map K L (A.atlas.restriction i i' hi')).comp (map K L (f.pullback i' j' h₂)) =
      (map K L (f.pullback i j h₁)).comp (map K L (B.atlas.restriction j j' hj'))
    simpa only [map_comp] using
      congrArg (map K L) (f.restriction_comm i i' j j' hi' hj' h₁ h₂)

/-- The extended pullbacks retain local compatibility on every actual
extended inverse-image domain. -/
theorem strongMap_compatible (f : StrongHom A B) (hf : f.HasLocallyCompatiblePullbacks) :
    (strongMap K L f hf).HasLocallyCompatiblePullbacks := by
  intro (i : A.atlas.Index) (j : B.atlas.Index) (k : B.atlas.Index) hj hk
    (m : B.atlas.Index) hmj hmk
  let BL := presentation K L B.atlas
  let hj₀ := (admissible_iff K L f hf i j).1 hj
  let hk₀ := (admissible_iff K L f hf i k).1 hk
  let hmj₀ := (range_chart_subset_iff K L B.atlas m j).1 hmj
  let hmk₀ := (range_chart_subset_iff K L B.atlas m k).1 hmk
  let D := B.atlas.restrictionDomain m j hmj₀
  let Q := Domain.pullback (f.pullback i j hj₀) D
  let DL := BL.atlas.restrictionDomain m j hmj
  let QL := Domain.pullback (map K L (f.pullback i j hj₀)) DL
  have hQ := domainPreservation.{u, u'} K L (A.atlas.algebra i) Q.algebra Q.baseMap Q.locus Q.represents
  have himage : HasImageIn L QL.baseMap
      (spectrumProjection K L (A.atlas.algebra i) ⁻¹' Q.locus) := by
    intro x
    have hx := QL.represents.hasImageIn x
    change (chartSystem K L B.atlas).chart j
        (BanachSpectrum.comap (map K L (f.pullback i j hj₀)).toBoundedRingHom
          (BanachSpectrum.comap QL.baseMap.toBoundedRingHom x)) ∈
      range ((chartSystem K L B.atlas).chart m) at hx
    rw [range_chart] at hx
    change B.atlas.chart j (spectrumProjection K L (B.atlas.algebra j)
        (BanachSpectrum.comap (map K L (f.pullback i j hj₀)).toBoundedRingHom
          (BanachSpectrum.comap QL.baseMap.toBoundedRingHom x))) ∈
      range (B.atlas.chart m) at hx
    rw [spectrumProjection_naturality] at hx
    exact hx
  obtain ⟨θ, hθ, _⟩ := hQ.2.2 QL.algebra QL.baseMap himage
  let α : BoundedAlgHom K (B.atlas.algebra m) Q.algebra :=
    Domain.pullbackMap (f.pullback i j hj₀) D
  have hα : α.comp (B.atlas.restriction m j hmj₀) =
      Q.baseMap.comp (f.pullback i j hj₀) :=
    Domain.pullbackMap_comp_baseMap (f.pullback i j hj₀) D
  have hαL : (map K L α).comp (map K L (B.atlas.restriction m j hmj₀)) =
      (map K L Q.baseMap).comp (map K L (f.pullback i j hj₀)) := by
    simpa only [map_comp] using congrArg (map K L) hα
  have hβ : θ.comp (map K L α) =
      Domain.pullbackMap (map K L (f.pullback i j hj₀)) DL := by
    apply DL.represents.hom_ext QL.algebra
    change (θ.comp (map K L α)).comp (map K L (B.atlas.restriction m j hmj₀)) =
      (Domain.pullbackMap (map K L (f.pullback i j hj₀)) DL).comp DL.baseMap
    rw [BoundedAlgHom.comp_assoc, hαL, ← BoundedAlgHom.comp_assoc, hθ]
    exact (Domain.pullbackMap_comp_baseMap (map K L (f.pullback i j hj₀)) DL).symm
  have hlocal₀ : Q.baseMap.comp (f.pullback i k hk₀) =
      α.comp (B.atlas.restriction m k hmk₀) := hf i j k hj₀ hk₀ m hmj₀ hmk₀
  have hlocal : (map K L Q.baseMap).comp (map K L (f.pullback i k hk₀)) =
      (map K L α).comp (map K L (B.atlas.restriction m k hmk₀)) := by
    simpa only [map_comp] using congrArg (map K L) hlocal₀
  change QL.baseMap.comp (map K L (f.pullback i k hk₀)) =
    (Domain.pullbackMap (map K L (f.pullback i j hj₀)) DL).comp
      (map K L (B.atlas.restriction m k hmk₀))
  rw [← hθ, BoundedAlgHom.comp_assoc, hlocal, ← BoundedAlgHom.comp_assoc, hβ]
  rfl

/-- Scalar extension as a complete compatible strong map. -/
def compatibleMap (f : CompatibleStrongHom A B) :
    CompatibleStrongHom (presentation K L A.atlas)
      (presentation K L B.atlas) where
  toStrongHom := strongMap K L f.toStrongHom f.compatible
  compatible := strongMap_compatible K L f.toStrongHom f.compatible

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
