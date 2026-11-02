import Langlands.AlgebraicGeometry.AlgebraicSpace.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Schemeness of algebraic spaces with a locally finite type monomorphism to a scheme

Stacks Project Lemma 67.27.10 (Tag 0463) and Proposition 67.50.2 (Tag 03XX): an
algebraic space with a monomorphism, locally of finite type, to a scheme is
represented by a scheme. Local finite type is expressed on one surjective etale atlas.
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- If an algebraic space `X` over `S` has a monomorphism `f` to the functor of points of
a scheme `Y` over `S`, and some surjective etale scheme atlas of `X` composed with `f` is
locally of finite type, then `X` is represented by a scheme. -/
def MonomorphismLocallyFiniteTypeSchemeStatement : Prop :=
  ∀ (S : Scheme.{u}) (X : AlgebraicSpace S) (Y : Over S)
    (f : X.presheaf ⟶ (schemeYoneda S).obj Y), Mono f →
    (∃ (W : Over S) (a : (schemeYoneda S).obj W ⟶ X.presheaf) (w : W ⟶ Y),
      IsEtale a ∧ IsSurjective a ∧ a ≫ f = (schemeYoneda S).map w ∧
        LocallyOfFiniteType w.left) →
    IsRepresentedByScheme X

end Langlands.AlgebraicGeometry.AlgebraicSpace
