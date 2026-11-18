import Langlands.Geometry.Analytic.FullRecognitionFiniteTargetRefinement
import Langlands.Geometry.Analytic.FiniteOpenModelChartBinding

/-! # Chart binding of target-local finite models in the recognized source atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A chart-change law in a locally refining subatlas holds in the whole
atlas: both laws determine the same constructed chart change. -/
theorem isMapChartChange_of_subatlas (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) {i j : {i : a.Index // P i}}
    {R : PresentedAffinoidAlgebra K} {φ : BoundedAlgHom K (a.algebra i.val) R}
    {ψ : BoundedAlgHom K (a.algebra j.val) R}
    (h : ∀ x : BanachSpectrum R,
      a.chart i.val (BanachSpectrum.comap φ.toBoundedRingHom x) ∈ range (a.chart j.val))
    (hψ : (a.subatlas P hP).IsMapChartChange i j R φ ψ) :
    a.IsMapChartChange i.val j.val R φ ψ := by
  have hc := a.changeMapChart_isMapChartChange i.val j.val R φ h
  have hc' : (a.subatlas P hP).IsMapChartChange i j R φ
      (a.changeMapChart i.val j.val R φ h) :=
    fun T η m hmi hmj α hα => hc T η m.val hmi hmj α hα
  have e := ((a.subatlas P hP).eq_changeMapChart i j R φ h ψ hψ).trans
    ((a.subatlas P hP).eq_changeMapChart i j R φ h _ hc').symm
  rw [e]
  exact hc

end Langlands.Analytic.IndexedAffinoidAtlas

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FamilyRefinement

open CategoryTheory Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas
open FiniteAffinoidAlgebraDescent

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {V : Set A.space} {U : Set B.space} {W : B.atlas.saturatedAtlas.RecognizedSubset}
  (F : g.FamilyRefinement V U W)

/-- The ambient trace of one refinement chart. -/
def piece (k : Fin F.size) : Set B.space := W.chart '' (F.domain k).locus

theorem piece_eq (k : Fin F.size) :
    F.piece k = range (B.atlas.saturatedAtlas.chart (F.index k)) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    obtain ⟨y, rfl⟩ := W.range_chart.symm.subset (F.index_subset_locus k hx)
    exact ⟨y, hx, rfl⟩

theorem piece_subset_target (k : Fin F.size) : F.piece k ⊆ (F.target k).locus :=
  (F.piece_eq k).subset.trans (F.index_subset_target k)

/-- The canonical target map of a refinement chart is an actual domain
restriction of its family member, through the identity pair system. -/
theorem canonicalPullback_represents (k : Fin F.size) :
    Represents K (F.models.rightCover.canonicalPullback k)
      ((F.target k).chart ⁻¹' F.piece k) := by
  let D := F.domain k
  let X := (StrongHom.id B.saturatedPresentation).domainRecognition W D
  have hX : (StrongHom.id B.saturatedPresentation).baseMap '' range X.chart ⊆
      range (F.target k).chart :=
    (StrongHom.id B.saturatedPresentation).domainRecognition_admissible W D (F.target k)
      (F.models.rightCover.image_subset_target k)
  have hXT : X.locus ⊆ (F.target k).locus := fun x hx =>
    F.models.rightCover.image_subset_target k ⟨x, hx, rfl⟩
  have e := AdmissiblePairSystem.pullback_congr (fullRecognitionPairs_id B) X (F.target k) hX hX
  have hr : Represents K
      ((StrongHom.id B.saturatedPresentation).fullRecognitionPairs.pullback X (F.target k) hX)
      ((F.target k).chart ⁻¹' X.locus) := by
    rw [e]
    exact X.restriction_represents (F.target k) hXT
  exact hr.postcomp_equiv ((StrongHom.id B.saturatedPresentation).domainRecognitionEquiv W D).symm

/-- The refinement chart as a domain of its family member, with the
canonical bounded map as structural map. -/
def targetDomain (k : Fin F.size) : Domain K (F.target k).algebra where
  algebra := (F.domain k).algebra
  baseMap := F.models.rightCover.canonicalPullback k
  locus := (F.target k).chart ⁻¹' F.piece k
  represents := F.canonicalPullback_represents k

/-- The finite local model as the pulled back domain of the finite left
recognized preimage. Its algebra and structural map are the local model's. -/
def leftDomain (k : Fin F.size) : Domain K (F.left k).algebra :=
  Domain.pullback (F.models.leftBase k) (F.targetDomain k)

theorem leftDomain_baseMap (k : Fin F.size) :
    (F.leftDomain k).baseMap = F.models.leftMap k := rfl

/-- The ambient chart of a local model through its finite left preimage. -/
def modelChart (k : Fin F.size) : C(BanachSpectrum (F.models.algebra k), A.space) :=
  (F.left k).chart.comp (F.leftDomain k).spectrumMap

theorem modelChart_apply (k : Fin F.size) (x : BanachSpectrum (F.models.algebra k)) :
    F.modelChart k x =
      (F.left k).chart (BanachSpectrum.comap (F.models.leftMap k).toBoundedRingHom x) := rfl

theorem mem_range_modelChart (k : Fin F.size) (z : A.space) :
    z ∈ range (F.modelChart k) ↔ z ∈ V ∧ g.baseMap z ∈ F.piece k := by
  have hcomm (y : BanachSpectrum (F.left k).algebra) :
      (F.target k).chart (BanachSpectrum.comap (F.models.leftBase k).toBoundedRingHom y) =
        g.baseMap ((F.left k).chart y) :=
    g.fullRecognitionPairs.chart_comm (F.left k) (F.target k) (F.left_admissible k) y
  have hloc : range (F.leftDomain k).spectrumMap = (F.leftDomain k).locus :=
    (F.leftDomain k).represents.2.1
  constructor
  · rintro ⟨x, rfl⟩
    have hx : (F.leftDomain k).spectrumMap x ∈ (F.leftDomain k).locus := hloc ▸ ⟨x, rfl⟩
    refine ⟨((F.left_locus k).subset
      ((F.left k).range_chart.subset ⟨_, rfl⟩)).1, ?_⟩
    have hx' : (F.target k).chart (BanachSpectrum.comap (F.models.leftBase k).toBoundedRingHom
        ((F.leftDomain k).spectrumMap x)) ∈ F.piece k := hx
    rw [hcomm] at hx'
    exact hx'
  · rintro ⟨hzV, hz⟩
    have hzL : z ∈ (F.left k).locus :=
      (F.left_locus k).symm.subset ⟨hzV, F.piece_subset_target k hz⟩
    obtain ⟨y, rfl⟩ := (F.left k).range_chart.symm.subset hzL
    have hy : y ∈ (F.leftDomain k).locus := by
      change (F.target k).chart
        (BanachSpectrum.comap (F.models.leftBase k).toBoundedRingHom y) ∈ F.piece k
      rw [hcomm]
      exact hz
    obtain ⟨x, rfl⟩ := hloc.symm.subset hy
    exact ⟨x, rfl⟩

theorem range_modelChart (k : Fin F.size) :
    range (F.modelChart k) = V ∩ g.baseMap ⁻¹' F.piece k := by
  ext z
  exact F.mem_range_modelChart k z

/-- A full domain of a local model as an actual local domain of the
recognized source atlas, with unchanged algebra. -/
def modelSubdomain (k : Fin F.size) (D : Domain K (F.models.algebra k)) :
    LocalDomain A.atlas.fullRecognitionAtlas :=
  ⟨F.left k, (F.leftDomain k).extend D⟩

theorem modelSubdomain_ambientMap (k : Fin F.size) (D : Domain K (F.models.algebra k))
    (x : BanachSpectrum D.algebra) :
    (F.modelSubdomain k D).ambientMap x = F.modelChart k (D.spectrumMap x) :=
  congrArg (F.left k).chart ((F.leftDomain k).extend_spectrumMap D x)

theorem modelSubdomain_locus (k : Fin F.size) (D : Domain K (F.models.algebra k)) :
    (F.modelSubdomain k D).locus = F.modelChart k '' D.locus :=
  (F.modelSubdomain k D).range_ambientMap.symm.trans
    ((congrArg range (funext (F.modelSubdomain_ambientMap k D))).trans
      ((range_comp (F.modelChart k) D.spectrumMap).trans
        (congrArg (fun S => F.modelChart k '' S) D.represents.2.1)))

/-- Extension retains every bounded restriction between domains of one model. -/
def modelSubdomainMap (k : Fin F.size) {D E : Domain K (F.models.algebra k)} (r : E ⟶ D) :
    F.modelSubdomain k E ⟶ F.modelSubdomain k D :=
  (LocalDomain.sameChartFunctor A.atlas.fullRecognitionAtlas (F.left k)).map
    ((F.leftDomain k).extendFunctor.map r)

theorem modelSubdomainMap_restriction (k : Fin F.size) {D E : Domain K (F.models.algebra k)}
    (r : E ⟶ D) : (F.modelSubdomainMap k r).restriction = r.restriction := rfl

/-- The whole local model as a local domain. -/
def modelDomain (k : Fin F.size) : LocalDomain A.atlas.fullRecognitionAtlas :=
  F.modelSubdomain k (Domain.whole K (F.models.algebra k))

theorem modelDomain_locus (k : Fin F.size) :
    (F.modelDomain k).locus = range (F.modelChart k) :=
  (F.modelSubdomain_locus k (Domain.whole K (F.models.algebra k))).trans image_univ

def modelIndex (k : Fin F.size) : A.atlas.fullRecognitionAtlas.saturatedAtlas.Index :=
  ⟨(F.modelDomain k).locus, ⟨_, rfl⟩⟩

theorem range_modelIndex (k : Fin F.size) :
    range (A.atlas.fullRecognitionAtlas.saturatedAtlas.chart (F.modelIndex k)) =
      range (F.modelChart k) :=
  (A.atlas.fullRecognitionAtlas.range_saturatedChart _).trans (F.modelDomain_locus k)

/-- The local model compared with its saturated chart algebra. -/
def modelEquiv (k : Fin F.size) :
    BoundedAlgEquiv K (F.models.algebra k)
      (A.atlas.fullRecognitionAtlas.saturatedAtlas.algebra (F.modelIndex k)) :=
  A.atlas.fullRecognitionAtlas.localDomainSaturatedEquiv (F.modelDomain k)

/-- The whole original overlap as a local domain inside the second model. -/
def overlapDomain (i j : Fin F.size) : LocalDomain A.atlas.fullRecognitionAtlas :=
  F.modelSubdomain j (F.models.modelOverlapDomain i j)

theorem overlapDomain_locus (i j : Fin F.size) :
    (F.overlapDomain i j).locus = range (F.modelChart i) ∩ range (F.modelChart j) := by
  refine (F.modelSubdomain_locus j (F.models.modelOverlapDomain i j)).trans ?_
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxE := (F.models.mem_modelOverlapDomain i j x).1 hx
    have hamb : g.baseMap (F.modelChart j x) =
        W.chart ((F.models.rightCover.cover.obj j).spectrumMap
          (BanachSpectrum.comap (F.models.rightMap j).toBoundedRingHom x)) :=
      F.models.ambient_condition j x
    refine ⟨(F.mem_range_modelChart i _).2 ⟨F.models.leftPoint_mem j x, ?_⟩, ⟨x, rfl⟩⟩
    rw [hamb]
    exact ⟨_, hxE.1, rfl⟩
  · rintro ⟨hzi, x, rfl⟩
    obtain ⟨-, y, hy, hyz⟩ := (F.mem_range_modelChart i _).1 hzi
    have hamb := F.models.ambient_condition j x
    have he : (F.models.rightCover.cover.obj j).spectrumMap
        (BanachSpectrum.comap (F.models.rightMap j).toBoundedRingHom x) = y :=
      W.isEmbedding_chart.injective (hamb.symm.trans hyz.symm)
    refine ⟨x, (F.models.mem_modelOverlapDomain i j x).2 ⟨he.symm ▸ hy, ?_⟩, rfl⟩
    exact (F.models.rightCover.cover.obj j).represents.hasImageIn _

def overlapIndex (i j : Fin F.size) : A.atlas.fullRecognitionAtlas.saturatedAtlas.Index :=
  ⟨(F.overlapDomain i j).locus, ⟨_, rfl⟩⟩

theorem range_overlapIndex (i j : Fin F.size) :
    range (A.atlas.fullRecognitionAtlas.saturatedAtlas.chart (F.overlapIndex i j)) =
      range (F.modelChart i) ∩ range (F.modelChart j) :=
  (A.atlas.fullRecognitionAtlas.range_saturatedChart _).trans (F.overlapDomain_locus i j)

theorem overlap_range (i j : Fin F.size) :
    range (A.atlas.fullRecognitionAtlas.saturatedAtlas.chart (F.overlapIndex i j)) =
      range (A.atlas.fullRecognitionAtlas.saturatedAtlas.chart (F.modelIndex i)) ∩
        range (A.atlas.fullRecognitionAtlas.saturatedAtlas.chart (F.modelIndex j)) :=
  (F.range_overlapIndex i j).trans
    (congrArg₂ (fun S T => S ∩ T) (F.range_modelIndex i).symm (F.range_modelIndex j).symm)

/-- The original overlap algebra compared with its saturated chart algebra. -/
def overlapEquiv (i j : Fin F.size) :
    BoundedAlgEquiv K (F.models.modelOverlapDomain i j).algebra
      (A.atlas.fullRecognitionAtlas.saturatedAtlas.algebra (F.overlapIndex i j)) :=
  A.atlas.fullRecognitionAtlas.localDomainSaturatedEquiv (F.overlapDomain i j)

theorem overlapDomain_subset_left (i j : Fin F.size) :
    (F.overlapDomain i j).locus ⊆ (F.modelDomain i).locus := by
  rw [F.overlapDomain_locus, F.modelDomain_locus]
  exact inter_subset_left

/-- The whole overlap restriction into the second model. -/
def overlapToModelRight (i j : Fin F.size) : F.overlapDomain i j ⟶ F.modelDomain j :=
  F.modelSubdomainMap j
    (show F.models.modelOverlapDomain i j ⟶ Domain.whole K (F.models.algebra j) from
      ⟨(F.models.modelOverlapDomain i j).baseMap, BoundedAlgHom.comp_id _⟩)

/-- The constructed restriction from the first model to the overlap is the
first matching restriction of the algebraic descent data. -/
theorem overlapToModelLeft_restriction (i j : Fin F.size) :
    (LocalDomain.Inclusion.ofSubset (F.overlapDomain i j) (F.modelDomain i)
      (F.overlapDomain_subset_left i j)).restriction = F.models.modelOverlapLeft i j := by
  let a := A.atlas.fullRecognitionAtlas
  let O := F.overlapDomain i j
  let N := F.modelDomain i
  have hsub := F.overlapDomain_subset_left i j
  have hc := a.domainSubset_chart O.index N.index O.domain N.domain hsub
  symm
  apply a.eq_domainRestriction_of_over_base O.index N.index O.domain N.domain hsub
  rw [a.domainChartRestriction_eq_changeMapChart O.index N.index O.domain hc]
  apply a.eq_changeMapChart
  exact a.isMapChartChange_of_subatlas g.recognitionSourceSelection
    g.recognitionSourceSelection_locallyRefining
    (i := F.models.leftIndex j) (j := F.models.leftIndex i)
    (a.domainBaseMap_image_chart O.index N.index O.domain hc)
    (F.models.modelOverlapLeft_isMapChartChange_left i j)

theorem overlapEquiv_left (i j : Fin F.size) :
    (A.atlas.fullRecognitionAtlas.saturatedAtlas.restriction (F.overlapIndex i j) (F.modelIndex i)
      ((F.overlap_range i j).subset.trans inter_subset_left)).comp
        (F.modelEquiv i).toBoundedAlgHom =
      (F.overlapEquiv i j).toBoundedAlgHom.comp (F.models.modelOverlapLeft i j) := by
  have hn := A.atlas.fullRecognitionAtlas.localDomainSaturatedEquiv_naturality
    (F.overlapDomain i j) (F.modelDomain i)
    (LocalDomain.Inclusion.ofSubset (F.overlapDomain i j) (F.modelDomain i)
      (F.overlapDomain_subset_left i j))
    ((F.overlap_range i j).subset.trans inter_subset_left)
  rw [F.overlapToModelLeft_restriction] at hn
  exact hn

theorem overlapEquiv_right (i j : Fin F.size) :
    (A.atlas.fullRecognitionAtlas.saturatedAtlas.restriction (F.overlapIndex i j) (F.modelIndex j)
      ((F.overlap_range i j).subset.trans inter_subset_right)).comp
        (F.modelEquiv j).toBoundedAlgHom =
      (F.overlapEquiv i j).toBoundedAlgHom.comp (F.models.modelOverlapDomain i j).baseMap :=
  A.atlas.fullRecognitionAtlas.localDomainSaturatedEquiv_naturality
    (F.overlapDomain i j) (F.modelDomain j) (F.overlapToModelRight i j)
    ((F.overlap_range i j).subset.trans inter_subset_right)

/-- The complete finite algebra descent diagram of the local models is bound
to actual saturated charts of the recognized source atlas. -/
def chartBinding :
    ChartBinding F.models.algebraDescentData.toPairTransitions
      A.atlas.fullRecognitionAtlas.saturatedAtlas :=
  ChartBinding.ofOverlapComparison F.models.algebraDescentData.toPairTransitions _
    F.modelIndex F.overlapIndex F.overlap_range F.modelEquiv
    (fun i j => (F.models.modelOverlapDomain i j).algebra)
    F.models.modelOverlapComparison F.overlapEquiv
    (fun i j => F.overlapEquiv_left i j)
    (fun i j => (F.overlapEquiv_right i j).trans
      (congrArg (fun z : BoundedAlgHom K (F.models.algebra j)
          (F.models.modelOverlapDomain i j).algebra =>
        (F.overlapEquiv i j).toBoundedAlgHom.comp z)
          (F.models.modelOverlapComparison_comp_localMap i j).symm))

theorem chartBinding_locus :
    F.chartBinding.gluingData.locus = ⋃ k, range (F.modelChart k) :=
  iUnion_congr F.range_modelIndex

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.FamilyRefinement
