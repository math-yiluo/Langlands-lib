import Langlands.Geometry.Analytic.GroundFieldExtensionCounterexample.WeakMap
import Langlands.Geometry.Analytic.GroundFieldExtensionAtlas

/-! # The Frobenius-twisted strong map does not extend to `F₄` -/

namespace Langlands.Analytic.GroundFieldExtensionCounterexample

open Set AffinoidAtlasPresentation
open PresentedAffinoidAlgebra.GroundFieldExtension

/-- No strong map between the presentations extended to `F₄` has, for every
pair of charts admissible for `weakMap`, an admissible pullback equal to the
ground field extension of the pullback of `weakMap`. -/
def NonExtensionStatement : Prop :=
  ¬∃ F : StrongHom
      (IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄
        sourceAtlasPresentation.atlas)
      (IndexedAffinoidAtlas.GroundFieldExtension.presentation F₂ F₄
        targetAtlasPresentation.atlas),
    ∀ (i : sourceAtlasPresentation.atlas.Index) (j : targetAtlasPresentation.atlas.Index)
      (h : weakMap.baseMap '' range (sourceAtlasPresentation.atlas.chart i) ⊆
        range (targetAtlasPresentation.atlas.chart j)),
      ∃ h', F.pullback i j h' = map F₂ F₄ (weakMap.pullback i j h)

end Langlands.Analytic.GroundFieldExtensionCounterexample
