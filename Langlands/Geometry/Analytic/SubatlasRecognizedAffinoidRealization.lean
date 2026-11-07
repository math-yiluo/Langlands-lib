import Langlands.Geometry.Analytic.SubatlasRecognizedRefinement
import Langlands.Geometry.Analytic.RecognizedAtlasExtension

/-! # Canonical selected-chart maps over arbitrary original recognized algebras -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P)

/-- Forget the selection proof on the actual chosen selected local-domain
representative and retain its literal locus as an original saturated index. -/
def subatlasSaturatedOriginalIndex (s : (a.subatlas P hP).saturatedAtlas.Index) :
    a.saturatedAtlas.Index :=
  ⟨(a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative s)).locus,
    ⟨_, rfl⟩⟩

theorem subatlasSaturatedOriginalIndex_range
    (s : (a.subatlas P hP).saturatedAtlas.Index) :
    Set.range (a.saturatedAtlas.chart (a.subatlasSaturatedOriginalIndex P hP s)) =
      Set.range ((a.subatlas P hP).saturatedAtlas.chart s) :=
  (a.range_saturatedChart _).trans
    ((a.subatlas P hP).saturatedRepresentative s).range_ambientMap.symm

/-- The actual equal-locus inclusion compares the unchanged selected
algebra with the representative chosen by the original saturation. -/
def subatlasSaturatedToOriginal (s : (a.subatlas P hP).saturatedAtlas.Index) :
    a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative s) ⟶
      a.saturatedRepresentative (a.subatlasSaturatedOriginalIndex P hP s) :=
  (LocalDomain.isoOfLocusEq _ _
    (a.saturatedRepresentative_locus (a.subatlasSaturatedOriginalIndex P hP s)).symm).hom

variable {P} (V : a.saturatedAtlas.RecognizedSubset)

/-- Every contained selected saturated chart is a full domain of the
original recognized algebra, by composing actual full representations. -/
def subatlasRecognizedChartDomain (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ V.locus) :
    Domain K V.algebra :=
  (V.originalDomain (a.subatlasSaturatedOriginalIndex P hP s)
    ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans hs)).extend
      (a.subatlasSaturatedToOriginal P hP s).relativeDomain

@[simp]
theorem subatlasRecognizedChartDomain_algebra
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ V.locus) :
    (a.subatlasRecognizedChartDomain hP V s hs).algebra =
      (a.subatlas P hP).saturatedAtlas.algebra s := rfl

theorem subatlasRecognizedChartDomain_baseMap
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ V.locus) :
    (a.subatlasRecognizedChartDomain hP V s hs).baseMap =
      (a.subatlasSaturatedToOriginal P hP s).restriction.comp
        (V.originalRestriction (a.subatlasSaturatedOriginalIndex P hP s)
          ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans hs)) := rfl

theorem subatlasRecognizedChartDomain_over_ambient
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ V.locus)
    (x : BanachSpectrum ((a.subatlas P hP).saturatedAtlas.algebra s)) :
    V.chart ((a.subatlasRecognizedChartDomain hP V s hs).spectrumMap x) =
      (a.subatlas P hP).saturatedAtlas.chart s x := by
  let S := a.subatlasSaturatedOriginalIndex P hP s
  let q := a.subatlasSaturatedToOriginal P hP s
  let C := V.originalDomain S ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans hs)
  have hc : (C.extend q.relativeDomain).spectrumMap x =
      C.spectrumMap (q.spectrumMap x) := BanachSpectrum.ext fun _ => rfl
  exact (congrArg V.chart hc).trans
    ((V.originalDomain_over_ambient S _ (q.spectrumMap x)).trans
      (q.ambientMap_naturality x))

theorem subatlasRecognizedChartDomain_locus
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ V.locus) :
    (a.subatlasRecognizedChartDomain hP V s hs).locus =
      V.chart ⁻¹' Set.range ((a.subatlas P hP).saturatedAtlas.chart s) := by
  let R := a.subatlasRecognizedChartDomain hP V s hs
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := R.represents.2.1.symm ▸ hx
    exact ⟨y, (a.subatlasRecognizedChartDomain_over_ambient hP V s hs y).symm.trans
      (congrArg V.chart hy)⟩
  · rintro ⟨y, hy⟩
    have h : R.spectrumMap y = x := V.isEmbedding_chart.injective
      ((a.subatlasRecognizedChartDomain_over_ambient hP V s hs y).trans hy)
    exact h ▸ R.represents.hasImageIn y

/-- Actual inclusion uniqueness and full subatlas restriction comparison
give naturality on the entire algebra, including nilpotent elements. -/
theorem subatlasRecognizedChartDomain_naturality
    (s t : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ V.locus)
    (ht : Set.range ((a.subatlas P hP).saturatedAtlas.chart t) ⊆ V.locus)
    (hst : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆
      Set.range ((a.subatlas P hP).saturatedAtlas.chart t)) :
    ((a.subatlas P hP).saturatedAtlas.restriction s t hst).comp
      (a.subatlasRecognizedChartDomain hP V t ht).baseMap =
        (a.subatlasRecognizedChartDomain hP V s hs).baseMap := by
  let S := a.subatlasSaturatedOriginalIndex P hP s
  let T := a.subatlasSaturatedOriginalIndex P hP t
  let L := a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative s)
  let q := a.subatlasSaturatedToOriginal P hP s
  let r := a.subatlasSaturatedToOriginal P hP t
  let f := (a.subatlasLocalDomainFunctor P hP).map
    ((a.subatlas P hP).saturatedInclusion s t hst)
  have hST : Set.range (a.saturatedAtlas.chart S) ⊆ Set.range (a.saturatedAtlas.chart T) :=
    (a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans
      (hst.trans (a.subatlasSaturatedOriginalIndex_range P hP t).symm.subset)
  let g := a.saturatedInclusion S T hST
  have he : f ≫ r = q ≫ g :=
    @Subsingleton.elim (LocalDomain.Inclusion L (a.saturatedRepresentative T))
      inferInstance _ _
  have hr := congrArg LocalDomain.Inclusion.restriction he
  change f.restriction.comp r.restriction = q.restriction.comp g.restriction at hr
  rw [a.subatlasLocalDomainFunctor_map_restriction] at hr
  let ws := V.originalRestriction S
    ((a.subatlasSaturatedOriginalIndex_range P hP s).subset.trans hs)
  let wt := V.originalRestriction T
    ((a.subatlasSaturatedOriginalIndex_range P hP t).subset.trans ht)
  have hn : g.restriction.comp wt = ws :=
    V.originalRestriction_naturality T S _ _ hST
  ext x
  exact (congrArg
    (fun h : BoundedAlgHom K (a.saturatedAtlas.algebra T)
      ((a.subatlas P hP).saturatedAtlas.algebra s) => h (wt x)) hr).trans
        (congrArg (fun h : BoundedAlgHom K V.algebra (a.saturatedAtlas.algebra S) =>
          q.restriction (h x)) hn)

/-- Canonical full maps on the finite chart indices constructed by
flattening the two successive full-domain covers. -/
def subatlasRecognitionCanonicalComponent
    (i : Fin (a.subatlasRecognitionDomainCover hP V).size) : Domain K V.algebra :=
  a.subatlasRecognizedChartDomain hP V (a.subatlasRecognitionChartIndex hP V i)
    (a.subatlasRecognitionChartIndex_subset hP V i)

theorem subatlasRecognitionCanonicalComponent_locus
    (i : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    (a.subatlasRecognitionCanonicalComponent hP V i).locus =
      V.chart ⁻¹' Set.range ((a.subatlas P hP).saturatedAtlas.chart
        (a.subatlasRecognitionChartIndex hP V i)) :=
  a.subatlasRecognizedChartDomain_locus hP V _ _

theorem subatlasRecognitionCanonicalComponent_over_ambient
    (i : Fin (a.subatlasRecognitionDomainCover hP V).size)
    (x : BanachSpectrum ((a.subatlas P hP).saturatedAtlas.algebra
      (a.subatlasRecognitionChartIndex hP V i))) :
    V.chart ((a.subatlasRecognitionCanonicalComponent hP V i).spectrumMap x) =
      (a.subatlas P hP).saturatedAtlas.chart (a.subatlasRecognitionChartIndex hP V i) x :=
  a.subatlasRecognizedChartDomain_over_ambient hP V _ _ x

/-- Actual pushout overlaps over the old recognized algebra become local
domains of the selected atlas by extension through the first representative. -/
def subatlasRecognitionOverlap (i j : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    LocalDomain (a.subatlas P hP) :=
  ((a.subatlas P hP).saturatedRepresentative (a.subatlasRecognitionChartIndex hP V i)).extend
    ((a.subatlasRecognitionCanonicalComponent hP V i).relative
      ((a.subatlasRecognitionCanonicalComponent hP V i).inter
        (a.subatlasRecognitionCanonicalComponent hP V j))
      ((a.subatlasRecognitionCanonicalComponent hP V i).interLeft
        (a.subatlasRecognitionCanonicalComponent hP V j)))

theorem subatlasRecognitionOverlap_locus
    (i j : Fin (a.subatlasRecognitionDomainCover hP V).size) :
    (a.subatlasRecognitionOverlap hP V i j).locus =
      Set.range ((a.subatlas P hP).saturatedAtlas.chart
        (a.subatlasRecognitionChartIndex hP V i)) ∩
      Set.range ((a.subatlas P hP).saturatedAtlas.chart
        (a.subatlasRecognitionChartIndex hP V j)) := by
  let E := a.subatlasRecognitionCanonicalComponent hP V i
  let F := a.subatlasRecognitionCanonicalComponent hP V j
  let Z := (a.subatlas P hP).saturatedRepresentative (a.subatlasRecognitionChartIndex hP V i)
  have hmap : Z.ambientMap = V.chart.comp E.spectrumMap :=
    ContinuousMap.ext fun x => (a.subatlasRecognitionCanonicalComponent_over_ambient hP V i x).symm
  have himage : (a.subatlasRecognitionOverlap hP V i j).locus =
      V.chart '' (E.inter F).locus := by
    calc
      _ = Z.ambientMap '' (E.relative (E.inter F) (E.interLeft F)).locus :=
        LocalDomain.extend_locus _ _
      _ = (V.chart.comp E.spectrumMap) '' (E.relative (E.inter F) (E.interLeft F)).locus :=
        congrArg (fun f : C(BanachSpectrum E.algebra, X) =>
          f '' (E.relative (E.inter F) (E.interLeft F)).locus) hmap
      _ = V.chart '' (E.spectrumMap '' (E.relative (E.inter F) (E.interLeft F)).locus) :=
        (Set.image_image V.chart E.spectrumMap
          (E.relative (E.inter F) (E.interLeft F)).locus).symm
      _ = V.chart '' (E.inter F).locus :=
        congrArg (fun S => V.chart '' S) (E.image_relative_locus _ _)
  apply himage.trans
  change V.chart '' (E.locus ∩ F.locus) = _
  dsimp only [E, F]
  rw [a.subatlasRecognitionCanonicalComponent_locus, a.subatlasRecognitionCanonicalComponent_locus]
  ext x
  constructor
  · rintro ⟨y, ⟨hyE, hyF⟩, rfl⟩
    exact ⟨hyE, hyF⟩
  · intro hx
    have hxV : x ∈ Set.range V.chart :=
      V.range_chart.symm ▸ a.subatlasRecognitionChartIndex_subset hP V i hx.1
    obtain ⟨y, rfl⟩ := hxV
    exact ⟨y, hx, rfl⟩

/-- The finite selected-saturation charts and their actual quotient overlaps. -/
def subatlasRecognitionGluing : FiniteChartGluingData (a.subatlas P hP).saturatedAtlas where
  size := (a.subatlasRecognitionDomainCover hP V).size
  index := a.subatlasRecognitionChartIndex hP V
  overlap i j := ⟨(a.subatlasRecognitionOverlap hP V i j).locus, ⟨_, rfl⟩⟩
  overlap_range i j :=
    ((a.subatlas P hP).range_saturatedChart _).trans
      (a.subatlasRecognitionOverlap_locus hP V i j)

theorem subatlasRecognitionGluing_locus :
    (a.subatlasRecognitionGluing hP V).locus = V.locus :=
  a.subatlasRecognitionChartIndex_covers hP V

/-- The original recognized algebra realizes the new finite charts with
the original ambient chart and equality of the entire bounded overlap maps. -/
def subatlasRecognitionAffinoidRealization :
    (a.subatlasRecognitionGluing hP V).AffinoidRealization where
  algebra := V.algebra
  chart := V.chart
  isEmbedding_chart := V.isEmbedding_chart
  range_chart := V.range_chart.trans (a.subatlasRecognitionGluing_locus hP V).symm
  restriction i := (a.subatlasRecognitionCanonicalComponent hP V i).baseMap
  restriction_chart i x := a.subatlasRecognitionCanonicalComponent_over_ambient hP V i x
  represents i := (a.subatlasRecognitionCanonicalComponent_locus hP V i) ▸
    (a.subatlasRecognitionCanonicalComponent hP V i).represents
  compatible i j := by
    let d := a.subatlasRecognitionGluing hP V
    have hO : Set.range ((a.subatlas P hP).saturatedAtlas.chart (d.overlap i j)) ⊆ V.locus :=
      (d.overlap_subset_left i j).trans (a.subatlasRecognitionChartIndex_subset hP V i)
    exact (a.subatlasRecognizedChartDomain_naturality hP V
      (d.overlap i j) (d.index i) hO (a.subatlasRecognitionChartIndex_subset hP V i)
        (d.overlap_subset_left i j)).trans
      (a.subatlasRecognizedChartDomain_naturality hP V
        (d.overlap i j) (d.index j) hO (a.subatlasRecognitionChartIndex_subset hP V j)
          (d.overlap_subset_right i j)).symm

end Langlands.Analytic.IndexedAffinoidAtlas
