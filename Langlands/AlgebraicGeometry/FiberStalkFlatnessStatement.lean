import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.RingTheory.TensorProduct.Basic

/-! # Flatness of a residue-field fibre map in terms of stalks -/

universe u

open CategoryTheory
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Derived from the first proof paragraph of Stacks Project Theorem 37.16.2 (tag 039C), applied
to the structure sheaf: let `f : X ⟶ Y` be a morphism of `S`-schemes, `x` a point of `X`,
`y = f x` and `s` the image of `y` in `S`. Put `R = 𝒪_{S,s}`, `A = 𝒪_{Y,y}` and `B = 𝒪_{X,x}`,
with the algebra structures given by the actual stalk maps `R → A → B`, `k = κ(s)` the residue
field of `R` and `F = A ⊗[R] k = A/𝔪_s A`. If the base change of `f` along
`Spec κ(s) ⟶ S` is flat, then `F ⊗[A] B = B/𝔪_s B` is a flat `F`-module.
This proposition is a statement target, not a proof of the bridge. -/
def FiberStalkFlatnessStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : Over S) (f : X ⟶ Y) (x : X.left),
    let y : Y.left := f.left x
    let s : S := Y.hom y
    let R : Type u := S.presheaf.stalk s
    let A : Type u := Y.left.presheaf.stalk y
    let B : Type u := X.left.presheaf.stalk x
    letI : Algebra R A := (Y.hom.stalkMap y).hom.toAlgebra
    letI : Algebra A B := (f.left.stalkMap x).hom.toAlgebra
    letI : Algebra R B := ((f.left.stalkMap x).hom.comp (Y.hom.stalkMap y).hom).toAlgebra
    let k : Type u := IsLocalRing.ResidueField R
    let F : Type u := A ⊗[R] k
    Flat ((Over.pullback (S.fromSpecResidueField s)).map f).left →
      Module.Flat F (F ⊗[A] B)

end Langlands.AlgebraicGeometry
