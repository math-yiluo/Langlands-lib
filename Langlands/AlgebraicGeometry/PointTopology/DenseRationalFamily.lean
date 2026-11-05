import Langlands.AlgebraicGeometry.PointTopology.RationalDensityExt

/-! # Dense indexed families of actual rational points -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k] {I : Type v}
    {X Y : Over (Spec (CommRingCat.of k))}

/-- A specified family of actual rational points has dense union of point images. -/
def HasDenseRationalPointFamily (p : I → RationalPoint k X) : Prop :=
  Dense (⋃ i : I, Set.range (p i).left)

/-- Equality can be detected on a specified dense rational-point family. -/
theorem hom_ext_of_denseRationalPointFamily [IsReduced X.left] [IsSeparated Y.hom]
    (p : I → RationalPoint k X) (hp : HasDenseRationalPointFamily p)
    {f g : X ⟶ Y} (h : ∀ i, p i ≫ f = p i ≫ g) : f = g := by
  have : IsDominant (equalizer.ι f g).left := by
    refine ⟨hp.mono ?_⟩
    intro x hx
    obtain ⟨i, a, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨(rationalPointEqualizerLift f g (p i) (h i)).left a, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left,
      rationalPointEqualizerLift_comp]
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated Y.hom
    ((Over.w f).trans (Over.w g).symm) (equalizer.ι f g).left
    (congrArg (fun q => q.left) (equalizer.condition f g))

end Langlands.AlgebraicGeometry.PointTopology
