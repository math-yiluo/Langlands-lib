import Langlands.Geometry.Analytic.FiniteBanachCancellation

/-! # Actual finite affinoid triangles over a common base -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Recognized inverse images of one common-base affinoid piece, with the
actual finite pullbacks and their composition identity. This records one
triangle; it does not assert finiteness over every middle target piece. -/
structure FiniteCommonBaseTriangle
    (g : StrongHom A.saturatedPresentation B.saturatedPresentation)
    (g' : StrongHom B.saturatedPresentation C.saturatedPresentation)
    (V : Set A.space) (U : Set B.space)
    (Z : C.atlas.saturatedAtlas.RecognizedSubset) where
  middle : B.atlas.saturatedAtlas.RecognizedSubset
  source : A.atlas.saturatedAtlas.RecognizedSubset
  middleToBase : g'.baseMap '' range middle.chart ⊆ range Z.chart
  sourceToMiddle : g.baseMap '' range source.chart ⊆ range middle.chart
  sourceToBase : (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap '' range source.chart ⊆ range Z.chart
  middle_locus : middle.locus = U ∩ g'.baseMap ⁻¹' Z.locus
  source_locus : source.locus = V ∩
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).baseMap ⁻¹' Z.locus
  source_preimage : source.locus = V ∩ g.baseMap ⁻¹' middle.locus
  middle_finite : (g'.fullRecognitionPairs.pullback middle Z middleToBase).IsFiniteBanach
  source_finite : (g.fullRecognitionPairs.pullback source middle sourceToMiddle).IsFiniteBanach
  pullback_comp :
    (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
        B.atlas.saturatedAtlas_hasAllLocalDomains).fullRecognitionPairs.pullback
          source Z sourceToBase =
      (g.fullRecognitionPairs.pullback source middle sourceToMiddle).comp
        (g'.fullRecognitionPairs.pullback middle Z middleToBase)

variable {g : StrongHom A.saturatedPresentation B.saturatedPresentation}
  {g' : StrongHom B.saturatedPresentation C.saturatedPresentation}
  {V : Set A.space} {U : Set B.space} {T : Set C.space}

/-- The two finite maps construct the recognized pieces of the common-base
triangle. Banach cancellation makes the actual intervening pullback finite. -/
theorem nonempty_finiteCommonBaseTriangle
    (hVU : g.baseMap '' V ⊆ U) (hg' : g'.IsFiniteOver U T)
    (hcomp : (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteOver V T)
    (Z : C.atlas.saturatedAtlas.RecognizedSubset) (hZT : Z.locus ⊆ T) :
    Nonempty (FiniteCommonBaseTriangle g g' V U Z) := by
  obtain ⟨P, hPZ, hP, hPfin⟩ := hg'.2 Z hZT
  obtain ⟨Q, hQZ, hQ, hQfin⟩ := hcomp.2 Z hZT
  have hQP : g.baseMap '' range Q.chart ⊆ range P.chart := by
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ Q.locus := Q.range_chart.subset hx
    have hyP : g.baseMap x ∈ P.locus := by
      rw [hQ] at hxQ
      rw [hP]
      exact ⟨hVU ⟨x, hxQ.1, rfl⟩, hxQ.2⟩
    exact P.range_chart.symm.subset hyP
  have hpre : Q.locus = V ∩ g.baseMap ⁻¹' P.locus := by
    rw [hQ, hP]
    ext x
    constructor
    · rintro ⟨hx, hz⟩
      exact ⟨hx, hVU ⟨x, hx, rfl⟩, hz⟩
    · rintro ⟨hx, -, hz⟩
      exact ⟨hx, hz⟩
  have htriangle := fullRecognitionPairs_comp g g' Q P Z hQP hPZ hQZ
  rw [htriangle] at hQfin
  exact ⟨⟨P, Q, hPZ, hQP, hQZ, hP, hQ, hpre, hPfin, hQfin.of_comp, htriangle⟩⟩

/-- Choose the actual finite common-base triangle from the finiteness of the
second map and the composite. No recognition or finiteness premise for `g`
is required. -/
def finiteCommonBaseTriangle
    (hVU : g.baseMap '' V ⊆ U) (hg' : g'.IsFiniteOver U T)
    (hcomp : (g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
      B.atlas.saturatedAtlas_hasAllLocalDomains).IsFiniteOver V T)
    (Z : C.atlas.saturatedAtlas.RecognizedSubset) (hZT : Z.locus ⊆ T) :
    FiniteCommonBaseTriangle g g' V U Z :=
  Classical.choice (nonempty_finiteCommonBaseTriangle hVU hg' hcomp Z hZT)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
