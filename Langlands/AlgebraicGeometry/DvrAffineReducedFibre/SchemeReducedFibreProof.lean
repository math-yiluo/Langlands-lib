import Langlands.AlgebraicGeometry.DvrAffineReducedFibre.SchemeReducedFibreStatement
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreTheorem
import StacksFrontier.RingTheory.Nagata.Defs

/-! # Proof of the scheme reduced fibre theorem from the Stacks copy -/

universe u v

namespace Langlands.AlgebraicGeometry.DvrAffineReducedFibre

/-- Proof of `SchemeReducedFibreStatement` (Stacks Project, Tag 09IL): the copy's theorem
`AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback`,
with the Nagata hypothesis assembled from its two fields. The conclusions agree by unfolding. -/
theorem schemeReducedFibre : SchemeReducedFibreStatement.{u, v} := by
  intro A _ _ K _ _ _ hA X f _ _ _
  have hA' : StacksIsNagataRing A :=
    ⟨hA.1, fun p _ => ⟨fun L _ _ _ _ _ => hA.2 p L⟩⟩
  obtain ⟨L, iL, iKL, hKL, iAL, hT, hW, h⟩ :=
    _root_.AlgebraicGeometry.exists_finiteExtension_smoothAt_genericPoints_fiber_normalization_pullback
      K hA' f
  exact ⟨L, iL, iKL, hKL, iAL, hT, hW, h⟩

end Langlands.AlgebraicGeometry.DvrAffineReducedFibre
