import Langlands.Geometry.Analytic.DomainEmbeddingSourceTransport
import Langlands.Geometry.Analytic.SaturatedEtaleProperty
import Langlands.Geometry.Analytic.InvariantAnalyticDomains

/-! # Source-open locality of canonical strong etaleness -/

noncomputable section

universe u v w

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory Topology Set PresentedAffinoidAlgebra IndexedAffinoidAtlas
  AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : SaturatedAtlasPresentation.{u, v, w} K}

/-- Actual domain inclusions fully represent the images of all original charts. -/
theorem domainInclusion_isDomainEmbedding (S : SaturatedAtlasPresentation.{u, v, w} K)
    (D : S.AnalyticDomain) : (S.domainInclusion D).IsDomainEmbedding := by
  refine ⟨IsEmbedding.subtypeVal, ?_⟩
  intro c j h
  change Represents K (S.presentation.atlas.restriction c.val j _)
    (S.presentation.atlas.chart j ⁻¹' (Subtype.val ''
      Set.range (S.presentation.atlas.subspaceChart D.carrier c)))
  have hr : Subtype.val '' Set.range (S.presentation.atlas.subspaceChart D.carrier c) =
      Set.range (S.presentation.atlas.chart c.val) := by
    rw [← Set.range_comp]
    rfl
  rw [hr]
  exact S.presentation.atlas.restriction_represents c.val j _

/-- Strong etaleness of the actual restriction to an open source domain
implies canonical all-pieces etaleness at every point in that domain. -/
theorem isEtaleAtAllPieces_of_strongEtale_openRestriction
    (f : A ⟶ B) (U : Set A.presentation.space) (hU : IsOpen U)
    (hf : strongEtale (A.domainInclusion (A.openDomain U hU) ≫ f))
    {y : A.presentation.space} (hy : y ∈ U) :
    (((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f) :
      AffinoidAtlasPresentation.StrongHom A.presentation.saturatedPresentation
        B.presentation.saturatedPresentation).IsEtaleAtAllPieces y := by
  let D := A.openDomain U hU
  let j := A.domainInclusion D
  let F := compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor (K := K)
  have hj := domainInclusion_isDomainEmbedding A D
  have hc := j.hasCoherentPullbacks_of_saturated (A.domain D).hasAllLocalDomains
  have ho : IsOpenEmbedding j.baseMap := hU.isOpenEmbedding_subtypeVal
  have hcomp : (F.map j).saturatedComp (F.map f)
      (A.domain D).presentation.atlas.saturatedAtlas_hasAllLocalDomains
      A.presentation.atlas.saturatedAtlas_hasAllLocalDomains = F.map (j ≫ f) := by
    exact (F.map_comp j f).symm
  have hp : ((j.saturationExtension hc).saturatedComp (F.map f)
      (A.domain D).presentation.atlas.saturatedAtlas_hasAllLocalDomains
      A.presentation.atlas.saturatedAtlas_hasAllLocalDomains).IsEtaleAtAllPieces
        (⟨y, hy⟩ : D.carrier) := by
    change ((F.map j).saturatedComp (F.map f) _ _).IsEtaleAtAllPieces _
    rw [hcomp]
    exact hf ⟨y, hy⟩
  exact StrongHom.IsDomainEmbedding.IsEtaleAtAllPieces.of_precomp_domainEmbedding
    hj hc ho hp

/-- Points possessing an actual open source restriction which is strongly etale. -/
def sourceOpenEtaleLocus (f : A ⟶ B) : Set A.presentation.space :=
  {y | ∃ (U : Set A.presentation.space) (hU : IsOpen U),
    y ∈ U ∧ strongEtale (A.domainInclusion (A.openDomain U hU) ≫ f)}

/-- The open-restriction locus is contained in the canonical all-pieces etale locus. -/
theorem isEtaleAtAllPieces_of_mem_sourceOpenEtaleLocus
    (f : A ⟶ B) {y : A.presentation.space} (hy : y ∈ sourceOpenEtaleLocus f) :
    (((compatibleFunctor ⋙ CompatibleAtlasPresentation.saturationFunctor).map f) :
      StrongHom A.presentation.saturatedPresentation B.presentation.saturatedPresentation).IsEtaleAtAllPieces y := by
  obtain ⟨U, hU, hy, hf⟩ := hy
  exact isEtaleAtAllPieces_of_strongEtale_openRestriction f U hU hf hy

/-- Canonical strong etaleness is local on an arbitrary open covering of the source. -/
theorem strongEtale_of_open_source_cover
    (f : A ⟶ B) {ι : Type*} (U : ι → Set A.presentation.space)
    (hU : ∀ i, IsOpen (U i)) (hcover : ∀ y, ∃ i, y ∈ U i)
    (hf : ∀ i, strongEtale (A.domainInclusion (A.openDomain (U i) (hU i)) ≫ f)) :
    strongEtale f := by
  intro y
  obtain ⟨i, hi⟩ := hcover y
  exact isEtaleAtAllPieces_of_mem_sourceOpenEtaleLocus f ⟨U i, hU i, hi, hf i⟩

end Langlands.Analytic.SaturatedAtlasPresentation
