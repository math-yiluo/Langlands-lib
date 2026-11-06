import Langlands.Geometry.Analytic.RecognizedAffinoidAtlas
import Langlands.Geometry.Analytic.AtlasSaturationComparison

/-! # Actual strong extension from an atlas to its recognized atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas.RecognizedSubset

variable {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (V : a.RecognizedSubset)

/-- Original chart restrictions commute with the actual maps from a
recognized presentation, as entire bounded algebra homomorphisms. -/
theorem originalRestriction_naturality (parent child : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.locus)
    (hc : Set.range (a.chart child) ⊆ V.locus)
    (h : Set.range (a.chart child) ⊆ Set.range (a.chart parent)) :
    (a.restriction child parent h).comp (V.originalRestriction parent hp) =
      V.originalRestriction child hc :=
  congrArg
    (fun q : BoundedAlgHom K V.val.SectionAlgebra (a.algebra child) =>
      q.comp V.property.algebraEquiv.toBoundedAlgHom)
    (V.val.gluingData.originalRestriction_naturality parent child
      (hp.trans V.val.gluingData_locus.symm.subset)
      (hc.trans V.val.gluingData_locus.symm.subset) h)

end IndexedAffinoidAtlas.RecognizedSubset

namespace AffinoidAtlasPresentation

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The constructed recognition atlas has the unchanged literal ambient
topological space. -/
def recognitionPresentation : AffinoidAtlasPresentation.{u, v, v} K where
  space := A.space
  atlas := A.atlas.recognitionAtlas

/-- Canonical universe reindexing permits independent ambient and original
index universes in the existing common-universe strong-map category. -/
def recognitionTarget : AffinoidAtlasPresentation.{u, v, max v w} K :=
  A.recognitionPresentation.reindex
    (Equiv.ulift : ULift.{w} A.atlas.RecognizedSubset ≃ A.atlas.RecognizedSubset)

/-- The actual all-admissible-pair strong extension. Every pullback is
the already constructed full-domain original restriction. -/
def toRecognition : StrongHom A.saturationSource A.recognitionTarget where
  baseMap := ContinuousMap.id A.space
  target_exists i := by
    refine ⟨ULift.up (A.atlas.originalRecognitionIndex i.down), ?_⟩
    change id '' Set.range (A.atlas.chart i.down) ⊆
      Set.range (A.atlas.recognitionAtlas.chart (A.atlas.originalRecognitionIndex i.down))
    rw [Set.image_id, A.atlas.recognitionAtlas_original_range]
  pullback i V h := V.down.originalRestriction i.down (by
    rw [← V.down.range_chart]
    change id '' Set.range (A.atlas.chart i.down) ⊆ Set.range V.down.chart at h
    simpa only [Set.image_id] using h)
  chart_comm i V h x := V.down.chart_originalRestriction i.down _ x
  restriction_comm i i' V V' hi hj h h' := by
    have hV : Set.range (A.atlas.chart i.down) ⊆ V.down.locus := by
      rw [← V.down.range_chart]
      change id '' Set.range (A.atlas.chart i.down) ⊆ Set.range V.down.chart at h
      simpa only [Set.image_id] using h
    have hV' : Set.range (A.atlas.chart i'.down) ⊆ V'.down.locus := by
      rw [← V'.down.range_chart]
      change id '' Set.range (A.atlas.chart i'.down) ⊆ Set.range V'.down.chart at h'
      simpa only [Set.image_id] using h'
    have hVV' : V.down.locus ⊆ V'.down.locus :=
      V.down.range_chart.symm.subset.trans (hj.trans V'.down.range_chart.subset)
    exact (V'.down.originalRestriction_naturality i'.down i.down hV'
      (hV.trans hVV') hi).trans
        (V.down.originalRestriction_comp_restriction V'.down hVV' i.down hV).symm

theorem toRecognition_baseMap :
    A.toRecognition.baseMap = ContinuousMap.id A.space := rfl

/-- The constructed map is an actual strong quasi-isomorphism: its
ambient map is the identity, and every admissible pullback represents
the required full relative affinoid domain. -/
theorem toRecognition_isQuasiIso : A.toRecognition.IsQuasiIso := by
  refine ⟨IsHomeomorph.id, ?_⟩
  intro i V h
  have hp : Set.range (A.atlas.chart i.down) ⊆ V.down.locus := by
    rw [← V.down.range_chart]
    change id '' Set.range (A.atlas.chart i.down) ⊆ Set.range V.down.chart at h
    simpa only [Set.image_id] using h
  change PresentedAffinoidAlgebra.Represents K
    (V.down.originalRestriction i.down hp)
    (V.down.chart ⁻¹' (id '' Set.range (A.atlas.chart i.down)))
  rw [Set.image_id]
  exact (V.down.originalDomain i.down hp).represents

end AffinoidAtlasPresentation
end Langlands.Analytic
