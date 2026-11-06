import Langlands.Geometry.Analytic.SubatlasFiniteDomainCover
import Langlands.Geometry.Analytic.SubatlasLocalDomainComparison
import Langlands.Geometry.Analytic.AtlasDomainTensorIntersection
import Langlands.Geometry.Analytic.FiniteChartAffinoidRealization

/-! # Actual finite selected-atlas realizations of original local full domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P)

/-- The selected saturation chooses an actual original local-domain
presentation, which can be included in any containing old local domain. -/
def subatlasSaturatedInclusion (U : LocalDomain a)
    (S : (a.subatlas P hP).saturatedAtlas.Index)
    (hS : Set.range ((a.subatlas P hP).saturatedAtlas.chart S) ⊆ U.locus) :
    a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative S) ⟶ U :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [a.subatlasLocalDomain_locus, ← LocalDomain.range_ambientMap]
    exact hS)

/-- A canonical full component over the unchanged old domain algebra;
its source is the actual chosen selected-saturation quotient algebra. -/
def subatlasSaturatedComponent (U : LocalDomain a)
    (S : (a.subatlas P hP).saturatedAtlas.Index)
    (hS : Set.range ((a.subatlas P hP).saturatedAtlas.chart S) ⊆ U.locus) :
    Domain K U.algebra :=
  (a.subatlasSaturatedInclusion P hP U S hS).relativeDomain

@[simp]
theorem subatlasSaturatedComponent_algebra (U : LocalDomain a)
    (S : (a.subatlas P hP).saturatedAtlas.Index)
    (hS : Set.range ((a.subatlas P hP).saturatedAtlas.chart S) ⊆ U.locus) :
    (a.subatlasSaturatedComponent P hP U S hS).algebra =
      (a.subatlas P hP).saturatedAtlas.algebra S := rfl

theorem subatlasSaturatedComponent_locus (U : LocalDomain a)
    (S : (a.subatlas P hP).saturatedAtlas.Index)
    (hS : Set.range ((a.subatlas P hP).saturatedAtlas.chart S) ⊆ U.locus) :
    (a.subatlasSaturatedComponent P hP U S hS).locus =
      U.ambientMap ⁻¹' Set.range ((a.subatlas P hP).saturatedAtlas.chart S) := by
  change U.ambientMap ⁻¹' ((a.subatlas P hP).saturatedRepresentative S).locus = _
  rw [← LocalDomain.range_ambientMap]
  rfl

theorem subatlasSaturatedComponent_over_ambient (U : LocalDomain a)
    (S : (a.subatlas P hP).saturatedAtlas.Index)
    (hS : Set.range ((a.subatlas P hP).saturatedAtlas.chart S) ⊆ U.locus)
    (x : BanachSpectrum ((a.subatlas P hP).saturatedAtlas.algebra S)) :
    U.ambientMap ((a.subatlasSaturatedComponent P hP U S hS).spectrumMap x) =
      (a.subatlas P hP).saturatedAtlas.chart S x :=
  (a.subatlasSaturatedInclusion P hP U S hS).ambientMap_naturality x

/-- The full selected-saturation bounded restrictions commute with the
canonical maps from every original local-domain container. -/
theorem subatlasSaturatedComponent_naturality (U : LocalDomain a)
    (S T : (a.subatlas P hP).saturatedAtlas.Index)
    (hS : Set.range ((a.subatlas P hP).saturatedAtlas.chart S) ⊆ U.locus)
    (hT : Set.range ((a.subatlas P hP).saturatedAtlas.chart T) ⊆ U.locus)
    (h : Set.range ((a.subatlas P hP).saturatedAtlas.chart S) ⊆
      Set.range ((a.subatlas P hP).saturatedAtlas.chart T)) :
    ((a.subatlas P hP).saturatedAtlas.restriction S T h).comp
      (a.subatlasSaturatedComponent P hP U T hT).baseMap =
        (a.subatlasSaturatedComponent P hP U S hS).baseMap := by
  let f := (a.subatlas P hP).saturatedInclusion S T h
  have he :
      (a.subatlasLocalDomainFunctor P hP).map f ≫
          a.subatlasSaturatedInclusion P hP U T hT =
        a.subatlasSaturatedInclusion P hP U S hS :=
    @Subsingleton.elim (LocalDomain.Inclusion
      (a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative S)) U)
      inferInstance _ _
  have hr := congrArg LocalDomain.Inclusion.restriction he
  change ((a.subatlasLocalDomainFunctor P hP).map f).restriction.comp
    (a.subatlasSaturatedComponent P hP U T hT).baseMap =
      (a.subatlasSaturatedComponent P hP U S hS).baseMap at hr
  rw [a.subatlasLocalDomainFunctor_map_restriction] at hr
  exact hr

namespace SelectedChartCover

variable {a P} {parent : a.Index} (c : a.SelectedChartCover P parent)
  (U : Domain K (a.algebra parent))

/-- Each actual selected local piece is an original chart of the
selected atlas's constructed local-domain saturation. -/
def saturatedDomainIndex (i : Fin c.size) : (a.subatlas P hP).saturatedAtlas.Index :=
  ⟨(c.selectedLocalPiece hP U i).locus, ⟨_, rfl⟩⟩

theorem saturatedDomainIndex_range (i : Fin c.size) :
    Set.range ((a.subatlas P hP).saturatedAtlas.chart (c.saturatedDomainIndex hP U i)) =
      (c.selectedLocalPiece hP U i).locus :=
  (a.subatlas P hP).range_saturatedChart _

theorem saturatedDomainIndex_subset (i : Fin c.size) :
    Set.range ((a.subatlas P hP).saturatedAtlas.chart (c.saturatedDomainIndex hP U i)) ⊆
      (⟨parent, U⟩ : LocalDomain a).locus := by
  rw [c.saturatedDomainIndex_range, c.selectedLocalPiece_locus]
  exact Set.inter_subset_left

/-- Canonical components use the selected saturation's actual chosen
algebras and the original local-domain restriction to the parent. -/
def saturatedDomainComponent (i : Fin c.size) : Domain K U.algebra :=
  a.subatlasSaturatedComponent P hP ⟨parent, U⟩
    (c.saturatedDomainIndex hP U i) (c.saturatedDomainIndex_subset hP U i)

theorem saturatedDomainComponent_locus (i : Fin c.size) :
    (c.saturatedDomainComponent hP U i).locus =
      (⟨parent, U⟩ : LocalDomain a).ambientMap ⁻¹'
        Set.range ((a.subatlas P hP).saturatedAtlas.chart
          (c.saturatedDomainIndex hP U i)) :=
  a.subatlasSaturatedComponent_locus P hP _ _ _

theorem saturatedDomainComponent_over_ambient (i : Fin c.size)
    (x : BanachSpectrum ((a.subatlas P hP).saturatedAtlas.algebra
      (c.saturatedDomainIndex hP U i))) :
    (⟨parent, U⟩ : LocalDomain a).ambientMap
        ((c.saturatedDomainComponent hP U i).spectrumMap x) =
      (a.subatlas P hP).saturatedAtlas.chart (c.saturatedDomainIndex hP U i) x :=
  a.subatlasSaturatedComponent_over_ambient P hP _ _ _ x

/-- The actual pushout quotient of two full components is a selected local
domain by extending it through the first chosen selected presentation. -/
def saturatedDomainOverlap (i j : Fin c.size) : LocalDomain (a.subatlas P hP) :=
  ((a.subatlas P hP).saturatedRepresentative (c.saturatedDomainIndex hP U i)).extend
    ((c.saturatedDomainComponent hP U i).relative
      ((c.saturatedDomainComponent hP U i).inter (c.saturatedDomainComponent hP U j))
      ((c.saturatedDomainComponent hP U i).interLeft (c.saturatedDomainComponent hP U j)))

/-- Its literal ambient subset is exactly the chart intersection. -/
theorem saturatedDomainOverlap_locus (i j : Fin c.size) :
    (c.saturatedDomainOverlap hP U i j).locus =
      Set.range ((a.subatlas P hP).saturatedAtlas.chart (c.saturatedDomainIndex hP U i)) ∩
        Set.range ((a.subatlas P hP).saturatedAtlas.chart
          (c.saturatedDomainIndex hP U j)) := by
  let E := c.saturatedDomainComponent hP U i
  let F := c.saturatedDomainComponent hP U j
  let Z := (a.subatlas P hP).saturatedRepresentative (c.saturatedDomainIndex hP U i)
  let A : LocalDomain a := ⟨parent, U⟩
  change (Z.extend (E.relative (E.inter F) (E.interLeft F))).locus = _
  have hmap : Z.ambientMap = A.ambientMap.comp E.spectrumMap :=
    ContinuousMap.ext fun x => (c.saturatedDomainComponent_over_ambient hP U i x).symm
  have himage : (Z.extend (E.relative (E.inter F) (E.interLeft F))).locus =
      A.ambientMap '' (E.inter F).locus := by
    calc
      _ = Z.ambientMap '' (E.relative (E.inter F) (E.interLeft F)).locus :=
        LocalDomain.extend_locus _ _
      _ = (A.ambientMap.comp E.spectrumMap) ''
          (E.relative (E.inter F) (E.interLeft F)).locus :=
        congrArg (fun f : C(BanachSpectrum E.algebra, X) =>
          f '' (E.relative (E.inter F) (E.interLeft F)).locus) hmap
      _ = A.ambientMap ''
          (E.spectrumMap '' (E.relative (E.inter F) (E.interLeft F)).locus) :=
        (Set.image_image A.ambientMap E.spectrumMap
          (E.relative (E.inter F) (E.interLeft F)).locus).symm
      _ = A.ambientMap '' (E.inter F).locus :=
        congrArg (fun S => A.ambientMap '' S) (E.image_relative_locus _ _)
  apply himage.trans
  change A.ambientMap '' (E.locus ∩ F.locus) = _
  dsimp only [E, F]
  rw [c.saturatedDomainComponent_locus, c.saturatedDomainComponent_locus]
  ext x
  constructor
  · rintro ⟨y, ⟨hyE, hyF⟩, rfl⟩
    exact ⟨hyE, hyF⟩
  · intro hx
    have hxA : x ∈ Set.range A.ambientMap :=
      A.range_ambientMap.symm ▸ c.saturatedDomainIndex_subset hP U i hx.1
    obtain ⟨y, rfl⟩ := hxA
    exact ⟨y, hx, rfl⟩

/-- All finite components and actual pushout overlaps are charts of the
selected saturation, with no supplied structure on their union. -/
def saturatedDomainGluing : FiniteChartGluingData (a.subatlas P hP).saturatedAtlas where
  size := c.size
  index := c.saturatedDomainIndex hP U
  overlap i j := ⟨(c.saturatedDomainOverlap hP U i j).locus, ⟨_, rfl⟩⟩
  overlap_range i j :=
    ((a.subatlas P hP).range_saturatedChart _).trans
      (c.saturatedDomainOverlap_locus hP U i j)

theorem saturatedDomainGluing_locus :
    (c.saturatedDomainGluing hP U).locus = (⟨parent, U⟩ : LocalDomain a).locus := by
  change (⋃ i, Set.range ((a.subatlas P hP).saturatedAtlas.chart
    (c.saturatedDomainIndex hP U i))) = _
  simp_rw [c.saturatedDomainIndex_range]
  exact c.selectedLocalPiece_covers hP U

/-- The old quotient algebra and its original ambient map realize the
constructed finite selected charts. Compatibility is equality of the
entire bounded restrictions by the mapped original inclusion triangles. -/
def saturatedDomainAffinoidRealization :
    (c.saturatedDomainGluing hP U).AffinoidRealization where
  algebra := U.algebra
  chart := (⟨parent, U⟩ : LocalDomain a).ambientMap
  isEmbedding_chart := (⟨parent, U⟩ : LocalDomain a).isEmbedding_ambientMap
  range_chart := (⟨parent, U⟩ : LocalDomain a).range_ambientMap.trans
    (c.saturatedDomainGluing_locus hP U).symm
  restriction i := (c.saturatedDomainComponent hP U i).baseMap
  restriction_chart i x := c.saturatedDomainComponent_over_ambient hP U i x
  represents i := (c.saturatedDomainComponent_locus hP U i) ▸
    (c.saturatedDomainComponent hP U i).represents
  compatible i j := by
    let d := c.saturatedDomainGluing hP U
    have hO : Set.range ((a.subatlas P hP).saturatedAtlas.chart (d.overlap i j)) ⊆
        (⟨parent, U⟩ : LocalDomain a).locus :=
      (d.overlap_subset_left i j).trans (c.saturatedDomainIndex_subset hP U i)
    exact (a.subatlasSaturatedComponent_naturality P hP ⟨parent, U⟩
      (d.overlap i j) (d.index i) hO (c.saturatedDomainIndex_subset hP U i)
      (d.overlap_subset_left i j)).trans
        (a.subatlasSaturatedComponent_naturality P hP ⟨parent, U⟩
          (d.overlap i j) (d.index j) hO (c.saturatedDomainIndex_subset hP U j)
          (d.overlap_subset_right i j)).symm

end SelectedChartCover

end Langlands.Analytic.IndexedAffinoidAtlas
