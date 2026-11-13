import Langlands.GroupScheme.ReducedBaseSmooth.Core

/-! # Transport of smooth residue fibres along base change and open immersions -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme.ReducedBaseSmooth

/-- In a pullback square, the residue fibre of the base-changed morphism at a point is a base
change of the residue fibre of the original morphism at the image point, so smoothness of
relative dimension `n` passes from the latter to the former. -/
theorem smoothOfRelativeDimension_fiber_of_isPullback {P X Y Z : Scheme.{u}} {fst : P ⟶ X}
    {snd : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (y : Y) (n : ℕ)
    (hf : SmoothOfRelativeDimension n (f.fiberToSpecResidueField (g y))) :
    SmoothOfRelativeDimension n (snd.fiberToSpecResidueField y) :=
  MorphismProperty.of_isPullback (isPullback_fiberToSpecResidueField_of_isPullback h y) hf

instance {T Z Y : Scheme.{u}} (p : Z ⟶ T) (i : Y ⟶ Z) [IsOpenImmersion i] (t : T) :
    IsOpenImmersion (fiberMap p i t) :=
  MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance rfl
    (Category.id_comp _).symm

/-- Restricting the source along an open immersion keeps residue fibres smooth of relative
dimension `n`: the new fibre is an open subscheme of the old one. -/
theorem smoothOfRelativeDimension_fiber_comp_of_isOpenImmersion {W X Y : Scheme.{u}}
    (j : W ⟶ X) [IsOpenImmersion j] (f : X ⟶ Y) (y : Y) (n : ℕ)
    (hf : SmoothOfRelativeDimension n (f.fiberToSpecResidueField y)) :
    SmoothOfRelativeDimension n ((j ≫ f).fiberToSpecResidueField y) := by
  rw [← fiberMap_fiberToSpecResidueField f j y]
  have := smoothOfRelativeDimension_comp (n := 0) (m := n) (fiberMap f j y)
    (f.fiberToSpecResidueField y)
  rwa [zero_add] at this

end Langlands.GroupScheme.ReducedBaseSmooth
