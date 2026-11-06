import Langlands.Geometry.Analytic.RecognizedDomainFiniteRefinement
import Langlands.Geometry.Analytic.FiniteChartAffinoidRealization
import Langlands.Geometry.Analytic.RecognizedAtlasExtension

/-! # Constructed finite affinoid realizations of recognized-chart domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

namespace RecognizedSubset

variable (V : a.RecognizedSubset) (D : Domain K V.algebra)

theorem domainLocus_subset : V.domainLocus D ⊆ V.locus := by
  rintro _ ⟨y, _, rfl⟩
  exact V.range_chart ▸ Set.mem_range_self y

/-- A contained original chart is an actual full subdomain of the unchanged
domain, by full-test factorization over the recognized algebra. -/
def domainOriginalInclusion (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.domainLocus D) :
    V.originalDomain parent (hp.trans (V.domainLocus_subset D)) ⟶ D :=
  Domain.inclusionOfSubset _ D (by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hp hx
    exact V.isEmbedding_chart.injective hyx ▸ hy)

/-- The original chart algebra is retained; its restriction from the domain
is constructed by the full representation of that domain. -/
def domainOriginalDomain (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.domainLocus D) : Domain K D.algebra :=
  D.relative _ (V.domainOriginalInclusion D parent hp)

@[simp]
theorem domainOriginalDomain_algebra (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.domainLocus D) :
    (V.domainOriginalDomain D parent hp).algebra = a.algebra parent := rfl

theorem domainOriginalDomain_baseMap_comp (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.domainLocus D) :
    (V.domainOriginalDomain D parent hp).baseMap.comp D.baseMap =
      V.originalRestriction parent (hp.trans (V.domainLocus_subset D)) :=
  (V.domainOriginalInclusion D parent hp).comp_baseMap

theorem domainOriginalDomain_locus (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.domainLocus D) :
    (V.domainOriginalDomain D parent hp).locus =
      V.domainAmbientMap D ⁻¹' Set.range (a.chart parent) := by
  rw [domainOriginalDomain, D.relative_locus_eq_preimage]
  rfl

theorem domainOriginalDomain_over_ambient (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.domainLocus D)
    (x : BanachSpectrum (a.algebra parent)) :
    V.domainAmbientMap D ((V.domainOriginalDomain D parent hp).spectrumMap x) =
      a.chart parent x := by
  change V.chart (D.spectrumMap
    ((V.domainOriginalInclusion D parent hp).spectrumMap x)) = _
  exact (congrArg V.chart
    ((V.domainOriginalInclusion D parent hp).spectrumMap_over_base x)).trans
      (V.originalDomain_over_ambient parent _ x)

/-- Compatibility is equality on all algebra elements, proved by cancellation
of the full domain map and original-restriction naturality. -/
theorem domainOriginalDomain_naturality (parent child : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.domainLocus D)
    (hc : Set.range (a.chart child) ⊆ V.domainLocus D)
    (h : Set.range (a.chart child) ⊆ Set.range (a.chart parent)) :
    (a.restriction child parent h).comp (V.domainOriginalDomain D parent hp).baseMap =
      (V.domainOriginalDomain D child hc).baseMap := by
  apply D.represents.hom_ext (a.algebra child)
  ext x
  have hparent := congrArg (fun f : BoundedAlgHom K V.algebra (a.algebra parent) => f x)
    (V.domainOriginalDomain_baseMap_comp D parent hp)
  have hchild := congrArg (fun f : BoundedAlgHom K V.algebra (a.algebra child) => f x)
    (V.domainOriginalDomain_baseMap_comp D child hc)
  have hnatural := congrArg (fun f : BoundedAlgHom K V.algebra (a.algebra child) => f x)
    (V.originalRestriction_naturality parent child
      (hp.trans (V.domainLocus_subset D)) (hc.trans (V.domainLocus_subset D)) h)
  exact (congrArg (a.restriction child parent h) hparent).trans
    (hnatural.trans hchild.symm)

end RecognizedSubset

variable (a) (V : a.saturatedAtlas.RecognizedSubset) (D : Domain K V.algebra)

/-- The actual finite original-local-domain pieces give literal indices
of the already constructed enlarged atlas. -/
def fullRecognitionDomainIndex (i : Fin V.property.cover.size) : a.saturatedAtlas.Index :=
  ⟨(a.fullRecognitionDomainPiece V D i).locus, ⟨_, rfl⟩⟩

theorem fullRecognitionDomainIndex_range (i : Fin V.property.cover.size) :
    Set.range (a.saturatedAtlas.chart (a.fullRecognitionDomainIndex V D i)) =
      (a.fullRecognitionDomainPiece V D i).locus :=
  a.range_saturatedChart _

theorem fullRecognitionDomainIndex_subset (i : Fin V.property.cover.size) :
    Set.range (a.saturatedAtlas.chart (a.fullRecognitionDomainIndex V D i)) ⊆
      V.domainLocus D := by
  rw [a.fullRecognitionDomainIndex_range, a.fullRecognitionDomainPiece_locus,
    V.domainLocalPiece_locus]
  exact Set.inter_subset_left

/-- Canonical full component domains over the unchanged domain algebra,
with the actual presentations chosen by the enlarged atlas. -/
def fullRecognitionDomainComponent (i : Fin V.property.cover.size) : Domain K D.algebra :=
  V.domainOriginalDomain D (a.fullRecognitionDomainIndex V D i)
    (a.fullRecognitionDomainIndex_subset V D i)

@[simp]
theorem fullRecognitionDomainComponent_algebra (i : Fin V.property.cover.size) :
    (a.fullRecognitionDomainComponent V D i).algebra =
      a.saturatedAtlas.algebra (a.fullRecognitionDomainIndex V D i) := rfl

theorem fullRecognitionDomainComponent_locus (i : Fin V.property.cover.size) :
    (a.fullRecognitionDomainComponent V D i).locus =
      V.domainAmbientMap D ⁻¹'
        Set.range (a.saturatedAtlas.chart (a.fullRecognitionDomainIndex V D i)) :=
  V.domainOriginalDomain_locus D _ _

theorem fullRecognitionDomainComponent_over_ambient (i : Fin V.property.cover.size)
    (x : BanachSpectrum (a.saturatedAtlas.algebra (a.fullRecognitionDomainIndex V D i))) :
    V.domainAmbientMap D ((a.fullRecognitionDomainComponent V D i).spectrumMap x) =
      a.saturatedAtlas.chart (a.fullRecognitionDomainIndex V D i) x :=
  V.domainOriginalDomain_over_ambient D _ _ x

/-- The actual pushout quotient of the two canonical full components,
extended through the first chosen original local-domain presentation. -/
def fullRecognitionDomainOverlap (i j : Fin V.property.cover.size) : LocalDomain a :=
  (a.saturatedRepresentative (a.fullRecognitionDomainIndex V D i)).extend
    ((a.fullRecognitionDomainComponent V D i).relative
      ((a.fullRecognitionDomainComponent V D i).inter (a.fullRecognitionDomainComponent V D j))
      ((a.fullRecognitionDomainComponent V D i).interLeft (a.fullRecognitionDomainComponent V D j)))

@[simp]
theorem fullRecognitionDomainOverlap_algebra (i j : Fin V.property.cover.size) :
    (a.fullRecognitionDomainOverlap V D i j).algebra =
      ((a.fullRecognitionDomainComponent V D i).inter
        (a.fullRecognitionDomainComponent V D j)).algebra := rfl

/-- The extended quotient has exactly the literal intersection of the two
chosen chart ranges, even when the ambient space is not Hausdorff. -/
theorem fullRecognitionDomainOverlap_locus (i j : Fin V.property.cover.size) :
    (a.fullRecognitionDomainOverlap V D i j).locus =
      Set.range (a.saturatedAtlas.chart (a.fullRecognitionDomainIndex V D i)) ∩
        Set.range (a.saturatedAtlas.chart (a.fullRecognitionDomainIndex V D j)) := by
  let E := a.fullRecognitionDomainComponent V D i
  let F := a.fullRecognitionDomainComponent V D j
  let U := a.saturatedRepresentative (a.fullRecognitionDomainIndex V D i)
  change (U.extend (E.relative (E.inter F) (E.interLeft F))).locus = _
  have hmap : U.ambientMap = (V.domainAmbientMap D).comp E.spectrumMap :=
    ContinuousMap.ext fun x => (a.fullRecognitionDomainComponent_over_ambient V D i x).symm
  have himage :
      (U.extend (E.relative (E.inter F) (E.interLeft F))).locus =
        V.domainAmbientMap D '' (E.inter F).locus := by
    calc
      _ = U.ambientMap '' (E.relative (E.inter F) (E.interLeft F)).locus :=
        LocalDomain.extend_locus _ _
      _ = ((V.domainAmbientMap D).comp E.spectrumMap) ''
          (E.relative (E.inter F) (E.interLeft F)).locus :=
        congrArg (fun f : C(BanachSpectrum E.algebra, X) =>
          f '' (E.relative (E.inter F) (E.interLeft F)).locus) hmap
      _ = V.domainAmbientMap D ''
          (E.spectrumMap '' (E.relative (E.inter F) (E.interLeft F)).locus) :=
        (Set.image_image (V.domainAmbientMap D) E.spectrumMap
          (E.relative (E.inter F) (E.interLeft F)).locus).symm
      _ = V.domainAmbientMap D '' (E.inter F).locus :=
        congrArg (fun S => V.domainAmbientMap D '' S) (E.image_relative_locus _ _)
  apply himage.trans
  change V.domainAmbientMap D '' (E.locus ∩ F.locus) = _
  dsimp only [E, F]
  rw [a.fullRecognitionDomainComponent_locus, a.fullRecognitionDomainComponent_locus]
  ext x
  constructor
  · rintro ⟨y, ⟨hyE, hyF⟩, rfl⟩
    exact ⟨hyE, hyF⟩
  · intro hx
    have hxD : x ∈ Set.range (V.domainAmbientMap D) :=
      (V.range_domainAmbientMap D).symm ▸ a.fullRecognitionDomainIndex_subset V D i hx.1
    obtain ⟨y, rfl⟩ := hxD
    exact ⟨y, hx, rfl⟩

/-- All finite components and represented overlaps are actual original
charts of the enlarged atlas; no affinoid structure on their union is assumed. -/
def fullRecognitionDomainGluing : FiniteChartGluingData a.saturatedAtlas where
  size := V.property.cover.size
  index := a.fullRecognitionDomainIndex V D
  overlap i j := ⟨(a.fullRecognitionDomainOverlap V D i j).locus, ⟨_, rfl⟩⟩
  overlap_range i j :=
    (a.range_saturatedChart _).trans (a.fullRecognitionDomainOverlap_locus V D i j)

theorem fullRecognitionDomainGluing_locus :
    (a.fullRecognitionDomainGluing V D).locus = V.domainLocus D := by
  change (⋃ i, Set.range (a.saturatedAtlas.chart (a.fullRecognitionDomainIndex V D i))) = _
  simp_rw [a.fullRecognitionDomainIndex_range]
  exact a.fullRecognitionDomainPiece_covers V D

/-- The actual domain presentation realizes the constructed finite charts.
Every bounded component map and full-test representation is constructed,
and entire-map compatibility follows from full-domain cancellation. -/
def fullRecognitionDomainAffinoidRealization :
    (a.fullRecognitionDomainGluing V D).AffinoidRealization where
  algebra := D.algebra
  chart := V.domainAmbientMap D
  isEmbedding_chart := V.isEmbedding_domainAmbientMap D
  range_chart := (V.range_domainAmbientMap D).trans (a.fullRecognitionDomainGluing_locus V D).symm
  restriction i := (a.fullRecognitionDomainComponent V D i).baseMap
  restriction_chart i x := a.fullRecognitionDomainComponent_over_ambient V D i x
  represents i := (a.fullRecognitionDomainComponent_locus V D i) ▸
    (a.fullRecognitionDomainComponent V D i).represents
  compatible i j := by
    let d := a.fullRecognitionDomainGluing V D
    have hO : Set.range (a.saturatedAtlas.chart (d.overlap i j)) ⊆ V.domainLocus D :=
      (d.overlap_subset_left i j).trans (a.fullRecognitionDomainIndex_subset V D i)
    exact (V.domainOriginalDomain_naturality D (d.index i) (d.overlap i j)
      (a.fullRecognitionDomainIndex_subset V D i) hO (d.overlap_subset_left i j)).trans
        (V.domainOriginalDomain_naturality D (d.index j) (d.overlap i j)
          (a.fullRecognitionDomainIndex_subset V D j) hO (d.overlap_subset_right i j)).symm

end Langlands.Analytic.IndexedAffinoidAtlas
