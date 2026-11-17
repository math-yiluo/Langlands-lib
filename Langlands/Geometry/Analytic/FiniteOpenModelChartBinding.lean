import Langlands.Geometry.Analytic.FiniteOpenOverlapCoefficients
import Langlands.Geometry.Analytic.FiniteAlgebraChartRecognition
import Langlands.Geometry.Analytic.FibreProductDomainCoefficients

/-! # Actual finite-open chart binding -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.ChartBinding

open CategoryTheory Set IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {R : PresentedAffinoidAlgebra K} {c : Domain.FiniteCover (Domain.whole K R)}
  {F : LocalAlgebras c} (t : PairTransitions F)
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Compose overlap comparisons while using the proved entire bounded
leg equations before expanding the concrete equivalences. -/
def ofOverlapComparison
    (index : Fin c.size → a.Index) (overlap : Fin c.size → Fin c.size → a.Index)
    (hrange : ∀ i j, range (a.chart (overlap i j)) =
      range (a.chart (index i)) ∩ range (a.chart (index j)))
    (μ : ∀ i, BoundedAlgEquiv K (F.algebra i) (a.algebra (index i)))
    (Q : Fin c.size → Fin c.size → PresentedAffinoidAlgebra K)
    (e : ∀ i j, BoundedAlgEquiv K
      (F.baseChange j (F.overlap i j) (F.overlapRight i j)) (Q i j))
    (ν : ∀ i j, BoundedAlgEquiv K (Q i j) (a.algebra (overlap i j)))
    (hL : ∀ i j, (a.restriction (overlap i j) (index i)
      ((hrange i j).subset.trans inter_subset_left)).comp (μ i).toBoundedAlgHom =
        (ν i j).toBoundedAlgHom.comp ((e i j).toBoundedAlgHom.comp (t.leftRestriction i j)))
    (hR : ∀ i j, (a.restriction (overlap i j) (index j)
      ((hrange i j).subset.trans inter_subset_right)).comp (μ j).toBoundedAlgHom =
        (ν i j).toBoundedAlgHom.comp ((e i j).toBoundedAlgHom.comp (t.rightRestriction i j))) :
    ChartBinding t a where
  index := index
  overlap := overlap
  overlap_range := hrange
  componentEquiv := μ
  overlapEquiv i j := (e i j).trans (ν i j)
  left_compatible i j := (hL i j).trans
    (BoundedAlgHom.comp_assoc (ν i j).toBoundedAlgHom
      (e i j).toBoundedAlgHom (t.leftRestriction i j)).symm
  right_compatible i j := (hR i j).trans
    (BoundedAlgHom.comp_assoc (ν i j).toBoundedAlgHom
      (e i j).toBoundedAlgHom (t.rightRestriction i j)).symm

end Langlands.Analytic.PresentedAffinoidAlgebra.FiniteAffinoidAlgebraDescent.ChartBinding

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

private theorem change_from_common_source
    {i j k : a.Index} {R : PresentedAffinoidAlgebra K}
    {φ : BoundedAlgHom K (a.algebra i) R}
    {ψ : BoundedAlgHom K (a.algebra j) R}
    {χ : BoundedAlgHom K (a.algebra k) R}
    (hφ : ∀ x : BanachSpectrum R,
      a.chart i (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ range (a.chart j))
    (hψ : a.IsMapChartChange i j R φ ψ)
    (hχ : a.IsMapChartChange i k R φ χ) :
    a.IsMapChartChange j k R ψ χ := by
  have he := a.eq_changeMapChart i j R φ hφ ψ hψ
  have hc := IndexedAffinoidAtlas.IsMapChartChange.trans a
    (i := j) (j := i) (k := k) (R := R)
    (φ := a.changeMapChart i j R φ hφ) (ψ := φ) (χ := χ)
    (a.changeMapChart_image_original i j R φ hφ)
    (a.changeMapChart_reverse_isMapChartChange i j R φ hφ) hχ
  rwa [← he] at hc

end Langlands.Analytic.IndexedAffinoidAtlas

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas
open FiniteAffinoidAlgebraDescent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  {f : StrongHom A.saturatedPresentation C.saturatedPresentation}
  {g : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R)
  (OA : Set A.space) (OB : Set B.space) (hOA : IsOpen OA) (hOB : IsOpen OB)
  [hOAT : T2Space OA] [hOBT : T2Space OB] (hV : V ⊆ OA) (hR : R.locus ⊆ OB)
  [Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)]

/-- The raw pair structural map into an unchanged local-model domain. -/
def modelAnchorMap (i : Fin M.rightCover.cover.size) (D : Domain K (M.algebra i)) :
    BoundedAlgHom K
      (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))
      D.algebra :=
  D.baseMap.comp (M.pairToModel i)

omit [Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)] in
theorem modelAnchorMap_comp_left (i : Fin M.rightCover.cover.size)
    (D : Domain K (M.algebra i)) :
    (M.modelAnchorMap i D).comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =
      D.baseMap.comp (M.leftMap i) :=
  congrArg (fun z => D.baseMap.comp z) (M.pairToModel_comp_leftMap i)

omit [Nonempty (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)] in
theorem modelAnchorMap_comp_right (i : Fin M.rightCover.cover.size)
    (D : Domain K (M.algebra i)) :
    (M.modelAnchorMap i D).comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =
      (D.baseMap.comp (M.rightMap i)).comp (M.rightRecognitionEquiv i).symm.toBoundedAlgHom :=
  congrArg (fun z => D.baseMap.comp z) (M.pairToModel_comp_rightMap i)

/-- The original first-factor coefficient law of the actual extension
through a raw good-pair container. -/
theorem modelSubdomain_change_left (i : Fin M.rightCover.cover.size)
    (D : Domain K (M.algebra i)) :
    f.recognitionSource.atlas.IsMapChartChange (M.pairIndex i).1.1
      (M.modelSubdomain OA OB hOA hOB hV hR i D).index.rep.1.1 D.algebra
      ((M.modelAnchorMap i D).comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)))
      ((M.modelSubdomain OA OB hOA hOB hV hR i D).domain.baseMap.comp
        (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap
          (M.modelSubdomain OA OB hOA hOB hV hR i D).index.rep)) := by
  let h := FibreProduct.range_subset_goodPairContainer f.compatibleRecognitionMap
    g.compatibleRecognitionMap (M.pairIndex i) (M.pairIndex_good OA OB hOA hOB hV hR i)
  have hc := (f.recognitionSource.atlas.changeMapChart_isMapChartChange
    (M.pairIndex i).1.1
    (FibreProduct.goodPairContainer f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)
      (M.pairIndex_good OA OB hOA hOB hV hR i)).rep.1.1
    (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))
    (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))
    (FibreProduct.leftPoint_mem_of_range_subset h)).comp
      f.recognitionSource.atlas (M.modelAnchorMap i D)
  have he := congrArg (fun z => (M.modelAnchorMap i D).comp z)
    (FibreProduct.rangeRestriction_comp_leftMap f.compatibleRecognitionMap
      g.compatibleRecognitionMap h)
  exact he ▸ hc

theorem modelSubdomain_change_right (i : Fin M.rightCover.cover.size)
    (D : Domain K (M.algebra i)) :
    g.recognitionSource.atlas.IsMapChartChange (M.pairIndex i).1.2
      (M.modelSubdomain OA OB hOA hOB hV hR i D).index.rep.1.2 D.algebra
      ((M.modelAnchorMap i D).comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)))
      ((M.modelSubdomain OA OB hOA hOB hV hR i D).domain.baseMap.comp
        (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap
          (M.modelSubdomain OA OB hOA hOB hV hR i D).index.rep)) := by
  let h := FibreProduct.range_subset_goodPairContainer f.compatibleRecognitionMap
    g.compatibleRecognitionMap (M.pairIndex i) (M.pairIndex_good OA OB hOA hOB hV hR i)
  have hc := (g.recognitionSource.atlas.changeMapChart_isMapChartChange
    (M.pairIndex i).1.2
    (FibreProduct.goodPairContainer f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)
      (M.pairIndex_good OA OB hOA hOB hV hR i)).rep.1.2
    (FibreProduct.algebra f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))
    (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))
    (FibreProduct.rightPoint_mem_of_range_subset h)).comp
      g.recognitionSource.atlas (M.modelAnchorMap i D)
  have he := congrArg (fun z => (M.modelAnchorMap i D).comp z)
    (FibreProduct.rangeRestriction_comp_rightMap f.compatibleRecognitionMap
      g.compatibleRecognitionMap h)
  exact he ▸ hc

include hOA hOB hV hR hOAT hOBT in
private theorem overlap_rawPoint_mem (i j : Fin M.rightCover.cover.size)
    (x : BanachSpectrum (M.modelOverlapDomain i j).algebra) :
    (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).chart
      (M.pairIndex j)
      (BanachSpectrum.comap (M.modelAnchorMap j (M.modelOverlapDomain i j)).toBoundedRingHom x) ∈
        range ((FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).chart
          (M.pairIndex i)) := by
  have hx := (M.overlapDomain OA OB hOA hOB hV hR i j).range_ambientMap.subset ⟨x, rfl⟩
  rw [M.overlapDomain_locus OA OB hOA hOB hV hR i j] at hx
  obtain ⟨y, hy⟩ := hx.1
  exact ⟨(M.pairAlgebraEquiv i).spectrumHomeomorph y,
    hy.trans (M.modelSubdomain_ambientMap OA OB hOA hOB hV hR j (M.modelOverlapDomain i j) x)⟩

/-- The first matching map, including its full nonreduced coefficients,
is an actual arrow from the whole original overlap to the first model. -/
private def overlapToModelLeftAux (i j : Fin M.rightCover.cover.size)
    (φ : BoundedAlgHom K (M.algebra i) (M.modelOverlapDomain i j).algebra)
    (hL0 : f.recognitionSource.atlas.IsMapChartChange (M.leftIndex j) (M.leftIndex i)
      (M.modelOverlapDomain i j).algebra
      ((M.modelOverlapDomain i j).baseMap.comp (M.leftMap j)) (φ.comp (M.leftMap i)))
    (hR0 : g.recognitionSource.atlas.IsMapChartChange (M.pairIndex j).1.2 (M.pairIndex i).1.2
      (M.modelOverlapDomain i j).algebra
      (((M.modelOverlapDomain i j).baseMap.comp (M.rightMap j)).comp
        (M.rightRecognitionEquiv j).symm.toBoundedAlgHom)
      ((φ.comp (M.rightMap i)).comp (M.rightRecognitionEquiv i).symm.toBoundedAlgHom)) :
    M.overlapDomain OA OB hOA hOB hV hR i j ⟶ M.modelDomain OA OB hOA hOB hV hR i := by
  let L := M.overlapDomain OA OB hOA hOB hV hR i j
  let N := M.modelDomain OA OB hOA hOB hV hR i
  let α := M.modelAnchorMap j (M.modelOverlapDomain i j)
  let β := M.pairToModel i
  have hsub : L.locus ⊆ N.locus :=
    (M.overlapDomain_locus OA OB hOA hOB hV hR i j).subset.trans
      (inter_subset_left.trans (M.modelDomain_locus OA OB hOA hOB hV hR i).symm.subset)
  have hL : f.recognitionSource.atlas.IsMapChartChange (M.pairIndex j).1.1 (M.pairIndex i).1.1
      L.algebra (α.comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex j)))
      ((φ.comp β).comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))) := by
    have hs := M.modelAnchorMap_comp_left j (M.modelOverlapDomain i j)
    have ht : (φ.comp β).comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =
        φ.comp (M.leftMap i) :=
      congrArg (fun z : BoundedAlgHom K (M.left i).algebra (M.algebra i) => φ.comp z)
        (M.pairToModel_comp_leftMap i)
    exact hs.symm ▸ ht.symm ▸ hL0
  have hR' : g.recognitionSource.atlas.IsMapChartChange (M.pairIndex j).1.2 (M.pairIndex i).1.2
      L.algebra (α.comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex j)))
      ((φ.comp β).comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i))) := by
    have hs := M.modelAnchorMap_comp_right j (M.modelOverlapDomain i j)
    have ht : (φ.comp β).comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)) =
        (φ.comp (M.rightMap i)).comp (M.rightRecognitionEquiv i).symm.toBoundedAlgHom :=
      congrArg (fun z : BoundedAlgHom K (M.rightRecognition i).algebra (M.algebra i) => φ.comp z)
        (M.pairToModel_comp_rightMap i)
    exact hs.symm ▸ ht.symm ▸ hR0
  have hLimage (x : BanachSpectrum L.algebra) :
      f.recognitionSource.atlas.chart (M.pairIndex j).1.1
        (BanachSpectrum.comap (α.comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex j))).toBoundedRingHom x) ∈
          range (f.recognitionSource.atlas.chart (M.pairIndex i).1.1) :=
    ((FibreProduct.mem_range_chart_iff f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i) _).1
      (M.overlap_rawPoint_mem OA OB hOA hOB hV hR i j x)).1
  have hRimage (x : BanachSpectrum L.algebra) :
      g.recognitionSource.atlas.chart (M.pairIndex j).1.2
        (BanachSpectrum.comap (α.comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex j))).toBoundedRingHom x) ∈
          range (g.recognitionSource.atlas.chart (M.pairIndex i).1.2) :=
    ((FibreProduct.mem_range_chart_iff f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i) _).1
      (M.overlap_rawPoint_mem OA OB hOA hOB hV hR i j x)).2
  have hLtarget := (M.modelSubdomain_change_left OA OB hOA hOB hV hR i
    (Domain.whole K (M.algebra i))).comp f.recognitionSource.atlas φ
  have hRtarget := (M.modelSubdomain_change_right OA OB hOA hOB hV hR i
    (Domain.whole K (M.algebra i))).comp g.recognitionSource.atlas φ
  have hLtotal := IndexedAffinoidAtlas.IsMapChartChange.trans f.recognitionSource.atlas
    (i := (M.pairIndex j).1.1) (j := (M.pairIndex i).1.1) (k := N.index.rep.1.1)
    (R := L.algebra) (φ := α.comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex j)))
    (ψ := (φ.comp β).comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)))
    (χ := (φ.comp N.domain.baseMap).comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap N.index.rep))
    hLimage hL hLtarget
  have hRtotal := IndexedAffinoidAtlas.IsMapChartChange.trans g.recognitionSource.atlas
    (i := (M.pairIndex j).1.2) (j := (M.pairIndex i).1.2) (k := N.index.rep.1.2)
    (R := L.algebra) (φ := α.comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex j)))
    (ψ := (φ.comp β).comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex i)))
    (χ := (φ.comp N.domain.baseMap).comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap N.index.rep))
    hRimage hR' hRtarget
  let hcontainer := FibreProduct.range_subset_goodPairContainer f.compatibleRecognitionMap
    g.compatibleRecognitionMap (M.pairIndex j) (M.pairIndex_good OA OB hOA hOB hV hR j)
  have hLfinal := IndexedAffinoidAtlas.change_from_common_source f.recognitionSource.atlas
    (i := (M.pairIndex j).1.1) (j := L.index.rep.1.1) (k := N.index.rep.1.1)
    (R := L.algebra) (φ := α.comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex j)))
    (ψ := L.domain.baseMap.comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap L.index.rep))
    (χ := (φ.comp N.domain.baseMap).comp (FibreProduct.leftMap f.compatibleRecognitionMap g.compatibleRecognitionMap N.index.rep))
    (fun x => FibreProduct.leftPoint_mem_of_range_subset hcontainer
      (BanachSpectrum.comap α.toBoundedRingHom x))
    (M.modelSubdomain_change_left OA OB hOA hOB hV hR j (M.modelOverlapDomain i j)) hLtotal
  have hRfinal := IndexedAffinoidAtlas.change_from_common_source g.recognitionSource.atlas
    (i := (M.pairIndex j).1.2) (j := L.index.rep.1.2) (k := N.index.rep.1.2)
    (R := L.algebra) (φ := α.comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap (M.pairIndex j)))
    (ψ := L.domain.baseMap.comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap L.index.rep))
    (χ := (φ.comp N.domain.baseMap).comp (FibreProduct.rightMap f.compatibleRecognitionMap g.compatibleRecognitionMap N.index.rep))
    (fun x => FibreProduct.rightPoint_mem_of_range_subset hcontainer
      (BanachSpectrum.comap α.toBoundedRingHom x))
    (M.modelSubdomain_change_right OA OB hOA hOB hV hR j (M.modelOverlapDomain i j)) hRtotal
  exact FibreProduct.localDomainInclusionOfLegs f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains L N hsub φ hLfinal hRfinal

/-- The first actual local-domain inclusion stores the unchanged complete
algebraic matching restriction. -/
def overlapToModelLeft (i j : Fin M.rightCover.cover.size) :
    M.overlapDomain OA OB hOA hOB hV hR i j ⟶ M.modelDomain OA OB hOA hOB hV hR i :=
  M.overlapToModelLeftAux OA OB hOA hOB hV hR i j (M.modelOverlapLeft i j)
    (M.modelOverlapLeft_isMapChartChange_left i j) (M.modelOverlapLeft_isMapChartChange_right i j)

theorem overlapToModelLeft_restriction (i j : Fin M.rightCover.cover.size) :
    (M.overlapToModelLeft OA OB hOA hOB hV hR i j).restriction =
      M.modelOverlapLeft i j := rfl

/-- Both full algebraic and geometric first overlap restrictions agree
after the original actual saturation comparisons. -/
theorem overlapEquiv_left (i j : Fin M.rightCover.cover.size) :
    ((M.chartGluing OA OB hOA hOB hV hR).leftRestriction i j).comp
        (M.modelEquiv OA OB hOA hOB hV hR i).toBoundedAlgHom =
      (M.overlapEquiv OA OB hOA hOB hV hR i j).toBoundedAlgHom.comp
        (M.modelOverlapLeft i j) :=
  (recognitionProductAtlas f g).localDomainSaturatedEquiv_naturality
    (M.overlapDomain OA OB hOA hOB hV hR i j) (M.modelDomain OA OB hOA hOB hV hR i)
    (M.overlapToModelLeft OA OB hOA hOB hV hR i j)
    ((M.chartGluing OA OB hOA hOB hV hR).overlap_subset_left i j)

/-- The complete original finite algebra descent diagram is bound to the
actual saturated model and whole-overlap charts of the unrestricted product. -/
def chartBinding :
    ChartBinding M.algebraDescentData.toPairTransitions (recognitionProductAtlas f g).saturatedAtlas :=
  ChartBinding.ofOverlapComparison M.algebraDescentData.toPairTransitions _
    (M.chartGluing OA OB hOA hOB hV hR).index
    (M.chartGluing OA OB hOA hOB hV hR).overlap
    (M.chartGluing OA OB hOA hOB hV hR).overlap_range
    (M.modelEquiv OA OB hOA hOB hV hR)
    (fun i j => (M.modelOverlapDomain i j).algebra)
    M.modelOverlapComparison (M.overlapEquiv OA OB hOA hOB hV hR)
    (fun i j => M.overlapEquiv_left OA OB hOA hOB hV hR i j)
    (fun i j => (M.overlapEquiv_right OA OB hOA hOB hV hR i j).trans
      (congrArg (fun z : BoundedAlgHom K (M.algebra j) (M.modelOverlapDomain i j).algebra =>
        (M.overlapEquiv OA OB hOA hOB hV hR i j).toBoundedAlgHom.comp z)
          (M.modelOverlapComparison_comp_localMap i j).symm))

theorem chartBinding_gluingData :
    (M.chartBinding OA OB hOA hOB hV hR).gluingData = M.chartGluing OA OB hOA hOB hV hR := rfl

theorem chartBinding_locus :
    (M.chartBinding OA OB hOA hOB hV hR).gluingData.locus =
      FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
        FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus :=
  M.chartGluing_locus OA OB hOA hOB hV hR

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FiniteOpenBaseChangeModels
