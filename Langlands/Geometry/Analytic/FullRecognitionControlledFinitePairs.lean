import Langlands.Geometry.Analytic.FullRecognitionAllPiecesRestriction
import Langlands.Geometry.Analytic.FieldValuedPoints

/-! # Controlled finite recognized chart pairs through prescribed points -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A point in a prescribed chart has a recognized rational piece inside
that chart and any prescribed ambient neighborhood. -/
theorem exists_recognized_mem_subset_chart (x : X) (t : a.Index)
    (ht : x ∈ range (a.chart t)) (O : Set X) (hO : O ∈ 𝓝 x) :
    ∃ W : a.saturatedAtlas.RecognizedSubset,
      x ∈ W.locus ∧ W.locus ⊆ O ∧ W.locus ⊆ range (a.chart t) := by
  obtain ⟨s, hs⟩ := ht
  have hpre : a.chart t ⁻¹' O ∈ 𝓝 s :=
    (a.isEmbedding_chart t).continuous.continuousAt.preimage_mem_nhds (hs ▸ hO)
  obtain ⟨d, hdN, hdO⟩ := RationalChart.exists_rational_neighborhood s _ hpre
  let D : LocalDomain a := ⟨t, d.toDomain⟩
  have hD : (a.recognizedLocalDomain D).locus = a.chart t '' d.locus :=
    a.recognizedLocalDomain_locus D
  refine ⟨a.recognizedLocalDomain D, ?_, ?_, ?_⟩
  · rw [hD]
    exact ⟨s, mem_of_mem_nhds hdN, hs⟩
  · rw [hD]
    rintro _ ⟨s', hs', rfl⟩
    exact hdO hs'
  · rw [hD]
    exact image_subset_range _ _

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation.StrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- Select a finite recognized pair at a prescribed point, retaining a
property stable under flat surjective restrictions and controlling both
ambient neighborhoods and the target original chart. -/
theorem HasAllPiecesAt.exists_pointed_fullRecognitionPair_within
    {Q : ∀ ⦃R S : PresentedAffinoidAlgebra K⦄,
      BoundedAlgHom K R S → BanachSpectrum S → Prop}
    (hpost : ∀ ⦃R S T : PresentedAffinoidAlgebra K⦄
      (r : BoundedAlgHom K S T) (f : BoundedAlgHom K R S) (z : BanachSpectrum T),
      r.toAlgHom.toRingHom.Flat → Function.Surjective r →
      f.toAlgHom.toRingHom.FiniteType →
      Q f (BanachSpectrum.comap r.toBoundedRingHom z) → Q (r.comp f) z)
    {y : A.space} (hg : g.HasAllPiecesAt Q y)
    (N : Set A.space) (hN : N ∈ 𝓝 y)
    (t : B.atlas.Index) (ht : g.baseMap y ∈ range (B.atlas.chart t))
    (O : Set B.space) (hO : O ∈ 𝓝 (g.baseMap y)) :
    ∃ (P : A.atlas.saturatedAtlas.RecognizedSubset)
      (W : B.atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' range P.chart ⊆ range W.chart)
      (s : BanachSpectrum P.algebra),
      P.chart s = y ∧ (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach ∧
      Q (g.fullRecognitionPairs.pullback P W h) s ∧
      P.locus ⊆ N ∧ W.locus ⊆ O ∧ W.locus ⊆ range (B.atlas.chart t) := by
  obtain ⟨V, U, -, hU, hyV, hVN, hfin, hQ⟩ := hg.exists_small hpost hN
  have hxU : g.baseMap y ∈ U := hfin.1 ⟨y, hyV, rfl⟩
  obtain ⟨W, hxW, hWUO, hWt⟩ := B.atlas.exists_recognized_mem_subset_chart
    (g.baseMap y) t ht (U ∩ O) (inter_mem (hU.mem_nhds hxU) hO)
  have hWU : W.locus ⊆ U := hWUO.trans inter_subset_left
  obtain ⟨P, h, hP, hfinite⟩ := hfin.2 W hWU
  have hyP : y ∈ range P.chart := by
    rw [P.range_chart, hP]
    exact ⟨hyV, hxW⟩
  obtain ⟨s, hs⟩ := hyP
  refine ⟨P, W, h, s, hs, hfinite, hQ W hWU hxW P h hP s hs, ?_,
    hWUO.trans inter_subset_right, hWt⟩
  exact (hP.trans_subset inter_subset_left).trans hVN

/-- The finite selector retains pointwise etaleness at the prescribed
source spectrum point. -/
theorem IsEtaleAtAllPieces.exists_pointed_fullRecognitionPair_within
    {y : A.space} (hg : g.IsEtaleAtAllPieces y)
    (N : Set A.space) (hN : N ∈ 𝓝 y)
    (t : B.atlas.Index) (ht : g.baseMap y ∈ range (B.atlas.chart t))
    (O : Set B.space) (hO : O ∈ 𝓝 (g.baseMap y)) :
    ∃ (P : A.atlas.saturatedAtlas.RecognizedSubset)
      (W : B.atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' range P.chart ⊆ range W.chart)
      (s : BanachSpectrum P.algebra),
      P.chart s = y ∧ (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach ∧
      (g.fullRecognitionPairs.pullback P W h).IsEtaleAtPoint s ∧
      P.locus ⊆ N ∧ W.locus ⊆ O ∧ W.locus ⊆ range (B.atlas.chart t) := by
  obtain ⟨V, -, hyV, he⟩ := hg
  have hQ : g.HasAllPiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) y :=
    hasAllPiecesAt_isEtaleAtPoint_iff.2 (he y hyV)
  refine hQ.exists_pointed_fullRecognitionPair_within ?_ N hN t ht O hO
  intro R S T r f z hr hsurj hft hf
  exact ⟨(r.isFlatAtPoint_of_flat hr z).comp hf.1,
    BoundedAlgHom.IsUnramifiedAtPoint.comp
      (RingHom.Finite.of_surjective _ hsurj).finiteType hft
      (r.isUnramifiedAtPoint_of_formallyUnramified
        (RingHom.FormallyUnramified.of_surjective hsurj) z) hf.2⟩

/-- Over a recognized target through the image point, choose a recognized
source piece through the prescribed point inside any given source chart. -/
theorem exists_pointed_fullRecognitionPair_over
    (g' : StrongHom C.saturatedPresentation B.saturatedPresentation)
    (z : C.space) (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (hzW : g'.baseMap z ∈ W.locus)
    (j : C.atlas.saturatedAtlas.Index)
    (hzj : z ∈ range (C.atlas.saturatedAtlas.chart j)) :
    ∃ (R : C.atlas.saturatedAtlas.RecognizedSubset)
      (_h : g'.baseMap '' range R.chart ⊆ range W.chart)
      (r : BanachSpectrum R.algebra),
      R.chart r = z ∧ R.locus ⊆ range (C.atlas.saturatedAtlas.chart j) := by
  have hzW' : g'.toFullRecognitionTarget.baseMap z ∈
      range (B.fullRecognitionPresentation.atlas.chart W) := by
    change g'.baseMap z ∈ range W.chart
    rw [W.range_chart]
    exact hzW
  obtain ⟨i, hzi, hiW⟩ := g'.toFullRecognitionTarget.exists_admissible_mem
    C.atlas.saturatedAtlas_hasAllLocalDomains z W hzW'
  obtain ⟨k, hk, hzk⟩ := IndexedAffinoidAtlas.exists_chart_inter hzi hzj
  let R : C.atlas.saturatedAtlas.RecognizedSubset :=
    C.atlas.saturatedAtlas.originalRecognitionIndex k
  have hR : range R.chart = range (C.atlas.saturatedAtlas.chart k) :=
    C.atlas.saturatedAtlas.recognitionAtlas_original_range k
  have h : g'.baseMap '' range R.chart ⊆ range W.chart :=
    (image_mono hR.subset).trans
      ((image_mono (hk.trans inter_subset_left)).trans hiW)
  have hzR : z ∈ range R.chart := hR.symm.subset hzk
  obtain ⟨r, hr⟩ := hzR
  refine ⟨R, h, r, hr, ?_⟩
  exact R.range_chart.symm.subset.trans (hR.subset.trans (hk.trans inter_subset_right))

/-- Chosen source points with the same ambient image have the same image
in the actual spectrum of a common recognized target. -/
theorem fullRecognitionPairs_comap_eq_of_chart_eq
    (g' : StrongHom C.saturatedPresentation B.saturatedPresentation)
    (P : A.atlas.saturatedAtlas.RecognizedSubset)
    (R : C.atlas.saturatedAtlas.RecognizedSubset)
    (W : B.atlas.saturatedAtlas.RecognizedSubset)
    (h : g.baseMap '' range P.chart ⊆ range W.chart)
    (h' : g'.baseMap '' range R.chart ⊆ range W.chart)
    (s : BanachSpectrum P.algebra) (r : BanachSpectrum R.algebra)
    (heq : g.baseMap (P.chart s) = g'.baseMap (R.chart r)) :
    BanachSpectrum.comap (g.fullRecognitionPairs.pullback P W h).toBoundedRingHom s =
      BanachSpectrum.comap (g'.fullRecognitionPairs.pullback R W h').toBoundedRingHom r := by
  apply W.isEmbedding_chart.injective
  exact (g.fullRecognitionPairs.chart_comm P W h s).trans
    (heq.trans (g'.fullRecognitionPairs.chart_comm R W h' r).symm)

/-- Controlled finite etale pieces and a second pointed piece over the same
recognized target, with equality in its actual spectrum. -/
def ControlledFiniteEtalePairsStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  ∀ (A B C : AffinoidAtlasPresentation.{u, v, w} K)
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (g' : StrongHom C.saturatedPresentation B.saturatedPresentation)
    (y : A.space) (z : C.space),
    g.IsEtaleAtAllPieces y → g.baseMap y = g'.baseMap z →
    ∀ (N : Set A.space), N ∈ 𝓝 y →
    ∀ (t : B.atlas.Index), g.baseMap y ∈ range (B.atlas.chart t) →
    ∀ (O : Set B.space), O ∈ 𝓝 (g.baseMap y) →
    ∀ (j : C.atlas.saturatedAtlas.Index), z ∈ range (C.atlas.saturatedAtlas.chart j) →
    ∃ (P : A.atlas.saturatedAtlas.RecognizedSubset)
      (R : C.atlas.saturatedAtlas.RecognizedSubset)
      (W : B.atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' range P.chart ⊆ range W.chart)
      (h' : g'.baseMap '' range R.chart ⊆ range W.chart)
      (s : BanachSpectrum P.algebra) (r : BanachSpectrum R.algebra),
      P.chart s = y ∧ R.chart r = z ∧
      (g.fullRecognitionPairs.pullback P W h).IsFiniteBanach ∧
      (g.fullRecognitionPairs.pullback P W h).IsEtaleAtPoint s ∧
      P.locus ⊆ N ∧ R.locus ⊆ range (C.atlas.saturatedAtlas.chart j) ∧
      W.locus ⊆ O ∧ W.locus ⊆ range (B.atlas.chart t) ∧
      BanachSpectrum.comap (g.fullRecognitionPairs.pullback P W h).toBoundedRingHom s =
        BanachSpectrum.comap (g'.fullRecognitionPairs.pullback R W h').toBoundedRingHom r

theorem controlledFiniteEtalePairs : ControlledFiniteEtalePairsStatement.{u, v, w} K := by
  intro A B C g g' y z hg heq N hN t ht O hO j hzj
  obtain ⟨P, W, h, s, hs, hfinite, hetale, hPN, hWO, hWt⟩ :=
    hg.exists_pointed_fullRecognitionPair_within N hN t ht O hO
  have hyW : g.baseMap y ∈ W.locus := by
    rw [← W.range_chart, ← hs]
    exact ⟨_, g.fullRecognitionPairs.chart_comm P W h s⟩
  obtain ⟨R, h', r, hr, hRj⟩ :=
    exists_pointed_fullRecognitionPair_over g' z W (heq ▸ hyW) j hzj
  refine ⟨P, R, W, h, h', s, r, hs, hr, hfinite, hetale, hPN, hRj, hWO, hWt, ?_⟩
  apply fullRecognitionPairs_comap_eq_of_chart_eq g' P R W h h' s r
  rw [hs, hr]
  exact heq

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic
