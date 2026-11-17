import Langlands.Geometry.Analytic.RecognizedContainedDomain
import Langlands.Geometry.Analytic.FullRecognitionControlledFinitePairs

/-! # Finite full-domain covers subordinate to recognized target pieces -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)

/-- An actual source full domain and its entire bounded map into one
recognized target piece contained in a prescribed ambient set. -/
structure OpenImagePiece (S : A.atlas.saturatedAtlas.Index) (U : Set B.space) where
  domain : Domain K (A.atlas.saturatedAtlas.algebra S)
  target : B.atlas.saturatedAtlas.RecognizedSubset
  target_subset : target.locus ⊆ U
  pullback : BoundedAlgHom K target.algebra domain.algebra
  chart_comm : ∀ x : BanachSpectrum domain.algebra,
    target.chart (BanachSpectrum.comap pullback.toBoundedRingHom x) =
      g.baseMap (A.atlas.saturatedAtlas.chart S (domain.spectrumMap x))

/-- Rational neighborhoods in an admissible target chart and their actual
full-domain pullbacks give a source neighborhood at every prescribed point. -/
theorem exists_openImagePiece_mem_nhds
    (S : A.atlas.saturatedAtlas.Index) (U : Set B.space) (hU : IsOpen U)
    (himage : g.baseMap '' range (A.atlas.saturatedAtlas.chart S) ⊆ U)
    (x : BanachSpectrum (A.atlas.saturatedAtlas.algebra S)) :
    ∃ d : g.OpenImagePiece S U, d.domain.locus ∈ 𝓝 x := by
  obtain ⟨T, hST⟩ := g.target_exists S
  change B.atlas.saturatedAtlas.Index at T
  let f : BoundedAlgHom K (B.atlas.saturatedAtlas.algebra T)
      (A.atlas.saturatedAtlas.algebra S) := g.pullback S T hST
  let y := BanachSpectrum.comap f.toBoundedRingHom x
  have hyU : B.atlas.saturatedAtlas.chart T y ∈ U :=
    (g.chart_comm S T hST x).symm ▸ himage ⟨_, mem_range_self x, rfl⟩
  have hN : B.atlas.saturatedAtlas.chart T ⁻¹' U ∈ 𝓝 y :=
    (B.atlas.saturatedAtlas.isEmbedding_chart T).continuous.continuousAt.preimage_mem_nhds
      (hU.mem_nhds hyU)
  obtain ⟨d, hdN, hdU⟩ := RationalChart.exists_rational_neighborhood y _ hN
  let L : LocalDomain B.atlas := (B.atlas.saturatedRepresentative T).extend d.toDomain
  let W : B.atlas.saturatedAtlas.RecognizedSubset := B.atlas.recognizedLocalDomain L
  have hW : W.locus = B.atlas.saturatedAtlas.chart T '' d.locus :=
    (B.atlas.recognizedLocalDomain_locus L).trans
      (LocalDomain.extend_locus (B.atlas.saturatedRepresentative T) d.toDomain)
  have hWT : W.locus ⊆ range (B.atlas.saturatedAtlas.chart T) :=
    hW.subset.trans (image_subset_range _ _)
  have hWU : W.locus ⊆ U := by
    rw [hW]
    rintro _ ⟨z, hz, rfl⟩
    exact hdU hz
  have hpre : B.atlas.saturatedAtlas.chart T ⁻¹' W.locus = d.locus := by
    rw [hW]
    exact preimage_image_eq _ (B.atlas.saturatedAtlas.isEmbedding_chart T).injective
  let D : Domain K (A.atlas.saturatedAtlas.algebra S) :=
    Domain.pullback f (W.containedDomain T hWT)
  let φ : BoundedAlgHom K W.algebra D.algebra :=
    Domain.pullbackMap f (W.containedDomain T hWT)
  have hcomp : φ.comp (W.containedRestriction T hWT) = D.baseMap.comp f :=
    Domain.pullbackMap_comp_baseMap f (W.containedDomain T hWT)
  have hc : ∀ z : BanachSpectrum D.algebra,
      W.chart (BanachSpectrum.comap φ.toBoundedRingHom z) =
        g.baseMap (A.atlas.saturatedAtlas.chart S (D.spectrumMap z)) := by
    intro z
    exact (W.chart_containedRestriction T hWT _).symm.trans
      ((congrArg (fun q : BoundedAlgHom K (B.atlas.saturatedAtlas.algebra T) D.algebra =>
        B.atlas.saturatedAtlas.chart T (BanachSpectrum.comap q.toBoundedRingHom z)) hcomp).trans
        (g.chart_comm S T hST (D.spectrumMap z)))
  refine ⟨⟨D, W, hWU, φ, hc⟩, ?_⟩
  change BanachSpectrum.comap f.toBoundedRingHom ⁻¹'
    (B.atlas.saturatedAtlas.chart T ⁻¹' W.locus) ∈ 𝓝 x
  exact (congrArg (fun L : Set (BanachSpectrum (B.atlas.saturatedAtlas.algebra T)) =>
    BanachSpectrum.comap f.toBoundedRingHom ⁻¹' L ∈ 𝓝 x) hpre).mpr
      ((BanachSpectrum.comapContinuous f.toBoundedRingHom).continuous.continuousAt.preimage_mem_nhds hdN)

/-- A finite full-domain cover of one actual source chart, with each entire
bounded map landing in a recognized target subset of the prescribed open set. -/
structure OpenImageChartCover (S : A.atlas.saturatedAtlas.Index) (U : Set B.space) where
  size : ℕ
  piece : Fin size → g.OpenImagePiece S U
  covers : ∀ x : BanachSpectrum (A.atlas.saturatedAtlas.algebra S),
    ∃ i, x ∈ (piece i).domain.locus

/-- Compactness collects the actual pulled-back target neighborhoods into
a finite source-domain cover. -/
private theorem nonempty_openImageChartCover
    (S : A.atlas.saturatedAtlas.Index) (U : Set B.space) (hU : IsOpen U)
    (himage : g.baseMap '' range (A.atlas.saturatedAtlas.chart S) ⊆ U) :
    Nonempty (g.OpenImageChartCover S U) := by
  classical
  choose d hd using g.exists_openImagePiece_mem_nhds S U hU himage
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun x => interior (d x).domain.locus) (fun _ => isOpen_interior)
    (fun x _ => mem_iUnion.mpr ⟨x, mem_interior_iff_mem_nhds.mpr (hd x)⟩)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨⟨Fintype.card I, fun i => d (e i).val, ?_⟩⟩
  intro x
  obtain ⟨y, hyI, hxy⟩ := mem_iUnion₂.mp (hI (mem_univ x))
  refine ⟨e.symm ⟨y, hyI⟩, ?_⟩
  simpa only [Equiv.apply_symm_apply] using interior_subset hxy

/-- The actual finite cover and all of its local bounded maps. -/
def openImageChartCover
    (S : A.atlas.saturatedAtlas.Index) (U : Set B.space) (hU : IsOpen U)
    (himage : g.baseMap '' range (A.atlas.saturatedAtlas.chart S) ⊆ U) :
    g.OpenImageChartCover S U :=
  Classical.choice (g.nonempty_openImageChartCover S U hU himage)

/-- A finite full-domain cover of an arbitrary recognized source affinoid,
retaining actual maps from recognized target affinoids contained in U. -/
structure RecognizedOpenImageCover
    (V : A.atlas.saturatedAtlas.RecognizedSubset) (U : Set B.space) where
  cover : Domain.FiniteCover (Domain.whole K V.algebra)
  target : Fin cover.size → B.atlas.saturatedAtlas.RecognizedSubset
  target_subset : ∀ i, (target i).locus ⊆ U
  pullback : ∀ i, BoundedAlgHom K (target i).algebra (cover.obj i).algebra
  chart_comm : ∀ i (x : BanachSpectrum (cover.obj i).algebra),
    (target i).chart (BanachSpectrum.comap (pullback i).toBoundedRingHom x) =
      g.baseMap (V.chart ((cover.obj i).spectrumMap x))

/-- Every recognized source affinoid whose image lies in U has a constructed
finite full-domain cover subordinate to actual recognized target pieces in U. -/
def recognizedOpenImageCover
    (V : A.atlas.saturatedAtlas.RecognizedSubset) (U : Set B.space) (hU : IsOpen U)
    (himage : g.baseMap '' V.locus ⊆ U) : g.RecognizedOpenImageCover V U := by
  classical
  let C (i : Fin V.property.cover.size) := g.openImageChartCover
    (V.property.cover.index i) U hU (fun y hy =>
      himage ((image_mono (V.component_subset i)) hy))
  let J := (i : Fin V.property.cover.size) × Fin (C i).size
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let D (k : Fin (Fintype.card J)) : Domain K V.algebra :=
    (V.property.componentDomain (e k).1).extend ((C (e k).1).piece (e k).2).domain
  let c : Domain.FiniteCover (Domain.whole K V.algebra) :=
    { size := Fintype.card J
      obj := D
      map k := ⟨(D k).baseMap, rfl⟩
      covers x _ := by
        obtain ⟨i, hi⟩ := V.componentCover.covers x (mem_univ x)
        obtain ⟨y, hy⟩ := (V.property.componentDomain i).represents.2.1.symm ▸ hi
        obtain ⟨j, hj⟩ := (C i).covers y
        refine ⟨e.symm ⟨i, j⟩, ?_⟩
        dsimp only [D]
        rw [Equiv.apply_symm_apply]
        exact ⟨y, hj, hy⟩ }
  refine ⟨c, fun k => ((C (e k).1).piece (e k).2).target,
    fun k => ((C (e k).1).piece (e k).2).target_subset,
    fun k => ((C (e k).1).piece (e k).2).pullback, ?_⟩
  intro k x
  exact (((C (e k).1).piece (e k).2).chart_comm x).trans
    (congrArg g.baseMap
      ((V.property.componentDomain_over_ambient (e k).1 _).symm.trans
        (congrArg V.chart (Domain.extend_spectrumMap (V.property.componentDomain (e k).1)
          ((C (e k).1).piece (e k).2).domain x)).symm))

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic
