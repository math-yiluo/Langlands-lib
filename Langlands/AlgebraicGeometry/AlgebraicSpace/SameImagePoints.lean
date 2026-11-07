import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic

/-! # Points of a scheme with the same image in a presheaf

For a morphism `a : h_U ⟶ X` from the functor of points of a scheme `U` over `S` to a presheaf
`X`, two points of `U` have the same image when one point of a test scheme maps to both of them
through two morphisms with equal composites in `X`. For an algebraic space `X` this says that
the two points map to the same point of `|X|`.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Two points `u` and `u'` of a scheme `U` over `S` have the same image under
`a : h_U ⟶ X` if some scheme `T` over `S` has morphisms `g, g' : T ⟶ U` with equal composites
`h_T ⟶ X` and a point `t` with `g t = u` and `g' t = u'`. -/
def SameImage {S : Scheme.{u}} {U : Over S} {X : Presheaf S}
    (a : (schemeYoneda S).obj U ⟶ X) (u u' : U.left) : Prop :=
  ∃ (T : Over S) (g g' : T ⟶ U) (t : T.left),
    (schemeYoneda S).map g ≫ a = (schemeYoneda S).map g' ≫ a ∧ g.left t = u ∧ g'.left t = u'

end Langlands.AlgebraicGeometry.AlgebraicSpace
