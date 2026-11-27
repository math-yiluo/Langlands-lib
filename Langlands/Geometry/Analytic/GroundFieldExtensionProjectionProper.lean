import Langlands.Geometry.Analytic.LocalizedGroundFieldExtension
import Mathlib.Topology.Maps.Proper.Basic

/-! # Proper projection from the scalar-extended analytic space -/

noncomputable section

universe u v w u'

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set Topology
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

local notation "C" => chartSystem K L a

private theorem chart_preimage_projection_image (i : a.Index) (Z : Set (C).Space) :
    a.chart i ⁻¹' (projection K L a '' Z) =
      spectrumProjection K L (a.algebra i) '' ((C).chart i ⁻¹' Z) := by
  ext x
  constructor
  · rintro ⟨z, hz, hzx⟩
    have hh : z ∈ range ((C).chart i) := (range_chart K L a i).symm ▸ ⟨x, hzx.symm⟩
    obtain ⟨y, rfl⟩ := hh
    refine ⟨y, hz, (a.isEmbedding_chart i).injective ?_⟩
    exact (projection_chart K L a i y).symm.trans hzx
  · rintro ⟨y, hy, rfl⟩
    exact ⟨(C).chart i y, hy, projection_chart K L a i y⟩

/-- The projection of the scalar-extended atlas is proper. Closedness is
checked on the target quasinet, and each fibre lies in one extended chart. -/
theorem projection_isProperMap : IsProperMap (projection K L a) := by
  refine isProperMap_iff_isClosedMap_and_compact_fibers.mpr
    ⟨continuous_projection K L a, ?_, ?_⟩
  · intro Z hZ
    apply (a.isNet_chartFamily.1.isClosed_iff _).mpr
    rintro _ ⟨i, rfl⟩
    let e := (a.isEmbedding_chart i).toHomeomorph
    apply e.isClosed_preimage.mp
    change IsClosed (a.chart i ⁻¹' (projection K L a '' Z))
    rw [chart_preimage_projection_image]
    exact ((hZ.preimage ((C).continuous_chart i)).isCompact.image
      (spectrumProjection K L (a.algebra i)).continuous).isClosed
  · intro x
    obtain ⟨i, s, rfl⟩ := mem_iUnion.mp (a.isNet_chartFamily.1.covers.symm ▸ mem_univ x)
    have hf : projection K L a ⁻¹' {a.chart i s} =
        (C).chart i '' (spectrumProjection K L (a.algebra i) ⁻¹' {s}) := by
      ext z
      constructor
      · intro hz
        have hzx : projection K L a z = a.chart i s := hz
        have hh : z ∈ range ((C).chart i) := (range_chart K L a i).symm ▸ ⟨s, hzx.symm⟩
        obtain ⟨t, rfl⟩ := hh
        exact ⟨t, (a.isEmbedding_chart i).injective
          ((projection_chart K L a i t).symm.trans hzx), rfl⟩
      · rintro ⟨t, ht, rfl⟩
        exact (projection_chart K L a i t).trans (congrArg (a.chart i) ht)
    rw [hf]
    exact (isClosed_singleton.preimage (spectrumProjection K L (a.algebra i)).continuous).isCompact.image
      ((C).continuous_chart i)

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open CategoryTheory Set Topology SaturatedAtlasPresentation
open IndexedAffinoidAtlas.GroundFieldExtension
open PresentedAffinoidAlgebra.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

/-- The natural scalar-extension projection as a continuous map of the original
point types. -/
def pointProjection (X : LocalizedCategory.{u, v, w} (K := K)) :
    C(localizedSpaceFunctor.obj ((localizedFunctor K L).obj X), localizedSpaceFunctor.obj X) where
  toFun z := ((localizedProjection K L).app X (ULift.up z)).down
  continuous_toFun := continuous_uliftDown.comp
    (((localizedProjection K L).app X).hom.continuous.comp continuous_uliftUp)

@[simp] theorem pointProjection_localization (A : SaturatedAtlasPresentation.{u, v, w} K)
    (z : (chartSystem K L A.presentation.atlas).Space) :
    pointProjection K L (localizationFunctor.obj A) z =
      projection K L A.presentation.atlas z := rfl

theorem pointProjection_naturality {X Y : LocalizedCategory.{u, v, w} (K := K)}
    (f : X ⟶ Y)
    (z : localizedSpaceFunctor.obj ((localizedFunctor K L).obj X)) :
    pointProjection K L Y (localizedSpaceFunctor.map ((localizedFunctor K L).map f) z) =
      localizedSpaceFunctor.map f (pointProjection K L X z) := by
  have h := (localizedProjection K L).naturality f
  have hpoint := congrArg (fun g => (g (ULift.up z)).down) h
  exact hpoint

/-- The natural projection in the localized category is a proper map of
underlying spaces, so inverse images of compact sets are compact. -/
theorem pointProjection_isProperMap (X : LocalizedCategory.{u, v, w} (K := K)) :
    IsProperMap (pointProjection K L X) := by
  obtain ⟨A, rfl⟩ := (localizedObjectEquiv (K := K)).surjective X
  exact projection_isProperMap K L A.presentation.atlas

theorem pointProjection_surjective (X : LocalizedCategory.{u, v, w} (K := K)) :
    Function.Surjective (pointProjection K L X) := by
  obtain ⟨A, rfl⟩ := (localizedObjectEquiv (K := K)).surjective X
  exact projection_surjective K L A.presentation.atlas

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
