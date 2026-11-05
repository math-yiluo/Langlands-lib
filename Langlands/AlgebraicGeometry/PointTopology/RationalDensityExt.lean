import Langlands.AlgebraicGeometry.PointTopology.RationalDensityStatement
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Morphism equality from dense actual rational points -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
    {X Y : Over (Spec (CommRingCat.of k))}

/-- An actual rational point on which two morphisms agree lifts to their
scheme-theoretic equalizer. -/
def rationalPointEqualizerLift (f g : X ⟶ Y) (p : RationalPoint k X)
    (hp : p ≫ f = p ≫ g) : RationalPoint k (equalizer f g) :=
  equalizer.lift p hp

@[simp]
theorem rationalPointEqualizerLift_comp (f g : X ⟶ Y) (p : RationalPoint k X)
    (hp : p ≫ f = p ≫ g) :
    rationalPointEqualizerLift f g p hp ≫ equalizer.ι f g = p :=
  equalizer.lift_ι p hp

/-- Morphisms from a reduced scheme to a separated scheme are determined by a
dense union of images of actual ground-field rational points. No finite-type
or algebraic-closure assumption is needed once this density is supplied. -/
theorem hom_ext_of_denseRationalPoints [IsReduced X.left] [IsSeparated Y.hom]
    (hX : HasDenseRationalPoints k X) {f g : X ⟶ Y}
    (h : ∀ p : RationalPoint k X, p ≫ f = p ≫ g) : f = g := by
  have : IsDominant (equalizer.ι f g).left := by
    refine ⟨hX.mono ?_⟩
    intro x hx
    obtain ⟨p, a, rfl⟩ := Set.mem_iUnion.mp hx
    refine ⟨(rationalPointEqualizerLift f g p (h p)).left a, ?_⟩
    rw [← Scheme.Hom.comp_apply, ← Over.comp_left,
      rationalPointEqualizerLift_comp]
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated Y.hom
    ((Over.w f).trans (Over.w g).symm) (equalizer.ι f g).left
    (congrArg (fun q => q.left) (equalizer.condition f g))

end Langlands.AlgebraicGeometry.PointTopology
