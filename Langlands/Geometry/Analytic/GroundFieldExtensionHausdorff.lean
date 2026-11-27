import Langlands.Geometry.Analytic.DisjointAffinoidAtlas
import Langlands.Geometry.Analytic.LocalizedGroundFieldExtension
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Scalar extension of Hausdorff analytic spaces -/

noncomputable section

universe u u' v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  {X : Type v} [TopologicalSpace X] [T2Space X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- The scalar extension of a Hausdorff analytic atlas has a Hausdorff space. -/
theorem t2Space_chartSystem : T2Space (chartSystem K L a).Space := by
  let b := atlas K L a
  apply (b.isNet_chartFamily.1.t2Space_iff b.isCompactFamily_chartFamily).mpr
  rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
  change a.Index at j
  have hclosed : IsClosed (range (b.chart j)) := by
    have h := (isCompact_range (a.isEmbedding_chart j).continuous).isClosed.preimage
      (continuous_projection K L a)
    exact (range_chart K L a j).symm ▸ h
  exact (isCompact_range (b.isEmbedding_chart i).continuous).inter_right hclosed

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- The object property specifying Hausdorff underlying spaces. -/
def hausdorffProperty : ObjectProperty (LocalizedCategory.{u, v, w} (K := K)) :=
  fun X => T2Space (localizedSpaceFunctor.obj X)

end Langlands.Analytic.SaturatedAtlasPresentation

namespace Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension

open _root_.CategoryTheory SaturatedAtlasPresentation
open IndexedAffinoidAtlas.GroundFieldExtension

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]

/-- Scalar extension in the analytic localization preserves Hausdorffness. -/
theorem hausdorff_localizedFunctor (X : LocalizedCategory.{u, v, w} (K := K))
    (hX : hausdorffProperty X) : hausdorffProperty ((localizedFunctor K L).obj X) := by
  obtain ⟨A, rfl⟩ := localizedObjectEquiv.surjective X
  let : T2Space A.presentation.space := hX
  exact t2Space_chartSystem K L A.presentation.atlas

/-- The scalar-extension functor on the full subcategories of Hausdorff analytic spaces. -/
def localizedHausdorffFunctor :
    (hausdorffProperty.{u, v, w} (K := K)).FullSubcategory ⥤
      (hausdorffProperty.{u', max u' w, max u' w} (K := L)).FullSubcategory :=
  hausdorffProperty.lift (hausdorffProperty.ι ⋙ localizedFunctor K L)
    (fun X => hausdorff_localizedFunctor K L X.obj X.property)

end Langlands.Analytic.AffinoidAtlasPresentation.GroundFieldExtension
