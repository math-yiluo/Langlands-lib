import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.CategoryTheory.Comma.Over.Pullback

/-! # The finite-presentation fibrewise flatness criterion -/

universe u

open CategoryTheory

namespace Langlands.AlgebraicGeometry

open _root_.AlgebraicGeometry

/-- Stacks Project tag 039E, Lemma 37.16.4, first assertion: a morphism `f : X ⟶ Y` of
`S`-schemes is flat if `X → S` is flat and locally of finite presentation, `Y → S` is locally
of finite type, and the base change `f_s : X_s ⟶ Y_s` of `f` along
`Spec κ(s) ⟶ S` is flat for every point `s` of `S`.
This proposition is a statement target, not a proof of the criterion. -/
def FiberwiseFlatnessStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : Over S) (f : X ⟶ Y),
    Flat X.hom → LocallyOfFinitePresentation X.hom → LocallyOfFiniteType Y.hom →
      (∀ s : S, Flat ((Over.pullback (S.fromSpecResidueField s)).map f).left) →
        Flat f.left

end Langlands.AlgebraicGeometry
