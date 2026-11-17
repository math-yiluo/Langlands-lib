import Langlands.Geometry.Analytic.FiniteOpenBaseChangeGeometry
import Langlands.Geometry.Analytic.FibreProductPairDomains
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBaseChange
import Langlands.Geometry.Analytic.FiniteChartGluingAlgebra

/-! # Actual saturated product chart data for finite-open local models -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Full-domain saturation comparisons retain every entire actual
local-domain arrow, by uniqueness of the two composite arrows. -/
theorem localDomainSaturatedEquiv_naturality
    (U V : LocalDomain a) (r : U ⟶ V)
    (h : range (a.saturatedAtlas.chart ⟨U.locus, ⟨U, rfl⟩⟩) ⊆
      range (a.saturatedAtlas.chart ⟨V.locus, ⟨V, rfl⟩⟩)) :
    (a.saturatedAtlas.restriction ⟨U.locus, ⟨U, rfl⟩⟩ ⟨V.locus, ⟨V, rfl⟩⟩ h).comp
        (a.localDomainSaturatedEquiv V).toBoundedAlgHom =
      (a.localDomainSaturatedEquiv U).toBoundedAlgHom.comp r.restriction := by
  let S : a.saturatedAtlas.Index := ⟨U.locus, ⟨U, rfl⟩⟩
  let T : a.saturatedAtlas.Index := ⟨V.locus, ⟨V, rfl⟩⟩
  let e := LocalDomain.isoOfLocusEq U (a.saturatedRepresentative S)
    (a.saturatedRepresentative_locus S).symm
  let e' := LocalDomain.isoOfLocusEq V (a.saturatedRepresentative T)
    (a.saturatedRepresentative_locus T).symm
  let s := a.saturatedInclusion S T h
  have he : s ≫ e'.inv = e.inv ≫ r :=
    @Subsingleton.elim (LocalDomain.Inclusion (a.saturatedRepresentative S) V) inferInstance _ _
  exact congrArg LocalDomain.Inclusion.restriction he

end Langlands.Analytic.IndexedAffinoidAtlas

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}
  (f : StrongHom A.saturatedPresentation C.saturatedPresentation)
  (g : StrongHom B.saturatedPresentation C.saturatedPresentation)

/-- The actual unrestricted product atlas of the canonical recognized
cospan; no global separation hypothesis is used. -/
abbrev recognitionProductAtlas :=
  FibreProduct.localAtlas f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains

namespace FiniteOpenBaseChangeModels

variable {f g}
  {V : Set A.space} {U : Set C.space} {R : B.atlas.saturatedAtlas.RecognizedSubset}
  (M : FiniteOpenBaseChangeModels f g V U R)
  (OA : Set A.space) (OB : Set B.space) (hOA : IsOpen OA) (hOB : IsOpen OB)
  [hOAT : T2Space OA] [hOBT : T2Space OB] (hV : V ⊆ OA) (hR : R.locus ⊆ OB)

include hOA hOB hV hR hOAT hOBT in
theorem pairIndex_good (i : Fin M.rightCover.cover.size) :
    M.pairIndex i ∈ FibreProduct.goodPairs f.compatibleRecognitionMap g.compatibleRecognitionMap := by
  refine ⟨OA, OB, hOA, hOB, hOAT, hOBT, ?_, ?_⟩
  · change range (M.left i).chart ⊆ OA
    exact (M.left i).range_chart.subset.trans fun x hx => hV ((M.left_locus i).subset hx).1
  · change range (M.rightRecognition i).chart ⊆ OB
    intro x hx
    obtain ⟨y, -, hy⟩ := (M.rightRecognition i).range_chart.subset hx
    exact hR (R.range_chart.subset ⟨y, hy⟩)

variable [Nonempty
  (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)]

/-- A full domain of an unchanged local model becomes an actual local
full domain of the original product atlas. Its algebra is unchanged. -/
def modelSubdomain (i : Fin M.rightCover.cover.size) (D : Domain K (M.algebra i)) :
    LocalDomain (recognitionProductAtlas f g) :=
  let L := FibreProduct.goodPairLocalDomain f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains (M.pairIndex i)
    (M.pairIndex_good OA OB hOA hOB hV hR i)
  ⟨L.index, L.domain.extend (Domain.transportBase (M.pairAlgebraEquiv i).symm D)⟩

theorem modelSubdomain_ambientMap (i : Fin M.rightCover.cover.size)
    (D : Domain K (M.algebra i)) (x : BanachSpectrum D.algebra) :
    (M.modelSubdomain OA OB hOA hOB hV hR i D).ambientMap x =
      M.productChart i (D.spectrumMap x) :=
  FibreProduct.goodPairLocalDomain_ambientMap f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains (M.pairIndex i)
    (M.pairIndex_good OA OB hOA hOB hV hR i)
    ((Domain.transportBase (M.pairAlgebraEquiv i).symm D).spectrumMap x)

theorem modelSubdomain_locus (i : Fin M.rightCover.cover.size)
    (D : Domain K (M.algebra i)) :
    (M.modelSubdomain OA OB hOA hOB hV hR i D).locus = M.productChart i '' D.locus := by
  exact (M.modelSubdomain OA OB hOA hOB hV hR i D).range_ambientMap.symm.trans
    ((congrArg range (funext (M.modelSubdomain_ambientMap OA OB hOA hOB hV hR i D))).trans
      ((range_comp (M.productChart i) D.spectrumMap).trans
        (congrArg (fun S => M.productChart i '' S) D.represents.2.1)))

/-- Extension and transport retain the whole bounded restriction on
every actual full domain of a fixed unchanged local model. -/
def modelSubdomainMap (i : Fin M.rightCover.cover.size)
    {D E : Domain K (M.algebra i)} (r : E ⟶ D) :
    M.modelSubdomain OA OB hOA hOB hV hR i E ⟶
      M.modelSubdomain OA OB hOA hOB hV hR i D :=
  let L := FibreProduct.goodPairLocalDomain f.compatibleRecognitionMap g.compatibleRecognitionMap
    f.recognitionSource_hasAllLocalDomains g.recognitionSource_hasAllLocalDomains
    C.fullRecognitionPresentation_hasAllLocalDomains (M.pairIndex i)
    (M.pairIndex_good OA OB hOA hOB hV hR i)
  (LocalDomain.sameChartFunctor (recognitionProductAtlas f g) L.index).map
    (L.domain.extendFunctor.map ((Domain.transportBaseFunctor (M.pairAlgebraEquiv i).symm).map r))

theorem modelSubdomainMap_restriction (i : Fin M.rightCover.cover.size)
    {D E : Domain K (M.algebra i)} (r : E ⟶ D) :
    (M.modelSubdomainMap OA OB hOA hOB hV hR i r).restriction = r.restriction := rfl

/-- Keep the entire unchanged local model as a full domain, rather than
retaining only its point set as an unrelated original algebra. -/
def modelDomain (i : Fin M.rightCover.cover.size) :
    LocalDomain (recognitionProductAtlas f g) :=
  M.modelSubdomain OA OB hOA hOB hV hR i (Domain.whole K (M.algebra i))

theorem modelDomain_locus (i : Fin M.rightCover.cover.size) :
    (M.modelDomain OA OB hOA hOB hV hR i).locus = range (M.productChart i) :=
  (M.modelSubdomain_locus OA OB hOA hOB hV hR i (Domain.whole K (M.algebra i))).trans image_univ

def modelIndex (i : Fin M.rightCover.cover.size) :
    (recognitionProductAtlas f g).saturatedAtlas.Index :=
  ⟨(M.modelDomain OA OB hOA hOB hV hR i).locus, ⟨_, rfl⟩⟩

theorem range_modelIndex (i : Fin M.rightCover.cover.size) :
    range ((recognitionProductAtlas f g).saturatedAtlas.chart
      (M.modelIndex OA OB hOA hOB hV hR i)) = range (M.productChart i) :=
  ((recognitionProductAtlas f g).range_saturatedChart _).trans
    (M.modelDomain_locus OA OB hOA hOB hV hR i)

/-- The actual local model algebra is compared with its chosen saturated
representative by full-domain uniqueness. -/
def modelEquiv (i : Fin M.rightCover.cover.size) :
    BoundedAlgEquiv K (M.algebra i)
      ((recognitionProductAtlas f g).saturatedAtlas.algebra
        (M.modelIndex OA OB hOA hOB hV hR i)) :=
  (recognitionProductAtlas f g).localDomainSaturatedEquiv
    (M.modelDomain OA OB hOA hOB hV hR i)

theorem modelEquiv_chart (i : Fin M.rightCover.cover.size)
    (x : BanachSpectrum ((recognitionProductAtlas f g).saturatedAtlas.algebra
      (M.modelIndex OA OB hOA hOB hV hR i))) :
    M.productChart i ((M.modelEquiv OA OB hOA hOB hV hR i).spectrumHomeomorph x) =
      (recognitionProductAtlas f g).saturatedAtlas.chart
        (M.modelIndex OA OB hOA hOB hV hR i) x := by
  let a := recognitionProductAtlas f g
  let L := M.modelDomain OA OB hOA hOB hV hR i
  let S := M.modelIndex OA OB hOA hOB hV hR i
  let e := LocalDomain.isoOfLocusEq L (a.saturatedRepresentative S)
    (a.saturatedRepresentative_locus S).symm
  exact (M.modelSubdomain_ambientMap OA OB hOA hOB hV hR i (Domain.whole K (M.algebra i))
    ((M.modelEquiv OA OB hOA hOB hV hR i).spectrumHomeomorph x)).symm.trans
      (e.inv.ambientMap_naturality x)

/-- The original closed-quotient base change of the second local model
to the literal original right-domain intersection. -/
def modelOverlapDomain (i j : Fin M.rightCover.cover.size) : Domain K (M.algebra j) :=
  Domain.pullback (M.rightMap j)
    ((M.rightCover.cover.obj j).relative
      ((M.rightCover.cover.obj i).inter (M.rightCover.cover.obj j))
      ((M.rightCover.cover.obj i).interRight (M.rightCover.cover.obj j)))

omit [Nonempty
  (FibreProduct.LocalAtlasIndex f.compatibleRecognitionMap g.compatibleRecognitionMap)] in
theorem mem_modelOverlapDomain (i j : Fin M.rightCover.cover.size)
    (x : BanachSpectrum (M.algebra j)) :
    x ∈ (M.modelOverlapDomain i j).locus ↔
      (M.rightCover.cover.obj j).spectrumMap
        (BanachSpectrum.comap (M.rightMap j).toBoundedRingHom x) ∈
          (M.rightCover.cover.obj i).locus ∩ (M.rightCover.cover.obj j).locus := by
  change BanachSpectrum.comap (M.rightMap j).toBoundedRingHom x ∈
    ((M.rightCover.cover.obj j).relative
      ((M.rightCover.cover.obj i).inter (M.rightCover.cover.obj j))
      ((M.rightCover.cover.obj i).interRight (M.rightCover.cover.obj j))).locus ↔ _
  rw [Domain.relative_locus_eq_preimage]
  rfl

/-- This local full-domain overlap retains the exact original iterated
pushout algebra required by finite algebra descent. -/
def overlapDomain (i j : Fin M.rightCover.cover.size) :
    LocalDomain (recognitionProductAtlas f g) :=
  M.modelSubdomain OA OB hOA hOB hV hR j (M.modelOverlapDomain i j)

/-- The whole actual overlap restriction into its second original local
model is retained before any saturation representative is selected. -/
def overlapToModelRight (i j : Fin M.rightCover.cover.size) :
    M.overlapDomain OA OB hOA hOB hV hR i j ⟶ M.modelDomain OA OB hOA hOB hV hR j :=
  M.modelSubdomainMap OA OB hOA hOB hV hR j
    (show M.modelOverlapDomain i j ⟶ Domain.whole K (M.algebra j) from
      ⟨(M.modelOverlapDomain i j).baseMap, BoundedAlgHom.comp_id _⟩)

theorem overlapDomain_locus (i j : Fin M.rightCover.cover.size) :
    (M.overlapDomain OA OB hOA hOB hV hR i j).locus =
      range (M.productChart i) ∩ range (M.productChart j) := by
  refine (M.modelSubdomain_locus OA OB hOA hOB hV hR j (M.modelOverlapDomain i j)).trans ?_
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxE := (M.mem_modelOverlapDomain i j x).1 hx
    have hxV := ((M.mem_range_productChart_iff j _).1 ⟨x, rfl⟩).1
    refine ⟨(M.mem_range_productChart_iff i _).2 ⟨hxV, ?_⟩, ⟨x, rfl⟩⟩
    exact ⟨_, hxE.1, (M.snd_productChart j x).symm⟩
  · rintro ⟨hzi, x, rfl⟩
    obtain ⟨y, hy, hyz⟩ := ((M.mem_range_productChart_iff i _).1 hzi).2
    have he : (M.rightCover.cover.obj j).spectrumMap
        (BanachSpectrum.comap (M.rightMap j).toBoundedRingHom x) = y :=
      R.isEmbedding_chart.injective ((M.snd_productChart j x).symm.trans hyz.symm)
    refine ⟨x, (M.mem_modelOverlapDomain i j x).2 ⟨he.symm ▸ hy, ?_⟩, rfl⟩
    exact (M.rightCover.cover.obj j).represents.hasImageIn _

def overlapIndex (i j : Fin M.rightCover.cover.size) :
    (recognitionProductAtlas f g).saturatedAtlas.Index :=
  ⟨(M.overlapDomain OA OB hOA hOB hV hR i j).locus, ⟨_, rfl⟩⟩

theorem range_overlapIndex (i j : Fin M.rightCover.cover.size) :
    range ((recognitionProductAtlas f g).saturatedAtlas.chart
      (M.overlapIndex OA OB hOA hOB hV hR i j)) =
        range (M.productChart i) ∩ range (M.productChart j) :=
  ((recognitionProductAtlas f g).range_saturatedChart _).trans
    (M.overlapDomain_locus OA OB hOA hOB hV hR i j)

/-- Full-domain uniqueness retains the entire original overlap algebra
when it is made an actual saturated product chart. -/
def overlapEquiv (i j : Fin M.rightCover.cover.size) :
    BoundedAlgEquiv K (M.modelOverlapDomain i j).algebra
      ((recognitionProductAtlas f g).saturatedAtlas.algebra
        (M.overlapIndex OA OB hOA hOB hV hR i j)) :=
  (recognitionProductAtlas f g).localDomainSaturatedEquiv
    (M.overlapDomain OA OB hOA hOB hV hR i j)

theorem overlapEquiv_chart (i j : Fin M.rightCover.cover.size)
    (x : BanachSpectrum ((recognitionProductAtlas f g).saturatedAtlas.algebra
      (M.overlapIndex OA OB hOA hOB hV hR i j))) :
    M.productChart j ((M.modelOverlapDomain i j).spectrumMap
      ((M.overlapEquiv OA OB hOA hOB hV hR i j).spectrumHomeomorph x)) =
        (recognitionProductAtlas f g).saturatedAtlas.chart
          (M.overlapIndex OA OB hOA hOB hV hR i j) x := by
  let a := recognitionProductAtlas f g
  let L := M.overlapDomain OA OB hOA hOB hV hR i j
  let S := M.overlapIndex OA OB hOA hOB hV hR i j
  let e := LocalDomain.isoOfLocusEq L (a.saturatedRepresentative S)
    (a.saturatedRepresentative_locus S).symm
  exact (M.modelSubdomain_ambientMap OA OB hOA hOB hV hR j (M.modelOverlapDomain i j)
    ((M.overlapEquiv OA OB hOA hOB hV hR i j).spectrumHomeomorph x)).symm.trans
      (e.inv.ambientMap_naturality x)

/-- Actual original model and whole-intersection indices give finite
chart gluing data in the actual saturated product atlas. -/
def chartGluing : FiniteChartGluingData (recognitionProductAtlas f g).saturatedAtlas where
  size := M.rightCover.cover.size
  index := M.modelIndex OA OB hOA hOB hV hR
  overlap := M.overlapIndex OA OB hOA hOB hV hR
  overlap_range i j :=
    (M.range_overlapIndex OA OB hOA hOB hV hR i j).trans
      (congrArg₂ (fun S T => S ∩ T)
        (M.range_modelIndex OA OB hOA hOB hV hR i).symm
        (M.range_modelIndex OA OB hOA hOB hV hR j).symm)

/-- The finite gluing locus is the entire literal finite preimage in the
actual unrestricted quotient, rather than an assumed affinoid parent. -/
theorem chartGluing_locus :
    (M.chartGluing OA OB hOA hOB hV hR).locus =
      FibreProduct.fst f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' V ∩
        FibreProduct.snd f.compatibleRecognitionMap g.compatibleRecognitionMap ⁻¹' R.locus := by
  exact (congrArg (fun F : Fin M.rightCover.cover.size →
    Set (FibreProduct.chartSystem f.compatibleRecognitionMap g.compatibleRecognitionMap).Space =>
      ⋃ i, F i) (funext (M.range_modelIndex OA OB hOA hOB hV hR))).trans
        (iUnion_range_productChart M)

/-- The actual original right overlap restriction commutes with the
whole bounded comparisons, on every coefficient of the local model. -/
theorem overlapEquiv_right (i j : Fin M.rightCover.cover.size) :
    ((M.chartGluing OA OB hOA hOB hV hR).rightRestriction i j).comp
        (M.modelEquiv OA OB hOA hOB hV hR j).toBoundedAlgHom =
      (M.overlapEquiv OA OB hOA hOB hV hR i j).toBoundedAlgHom.comp
        (M.modelOverlapDomain i j).baseMap :=
  (recognitionProductAtlas f g).localDomainSaturatedEquiv_naturality
    (M.overlapDomain OA OB hOA hOB hV hR i j) (M.modelDomain OA OB hOA hOB hV hR j)
    (M.overlapToModelRight OA OB hOA hOB hV hR i j)
    ((M.chartGluing OA OB hOA hOB hV hR).overlap_subset_right i j)

end FiniteOpenBaseChangeModels
end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
