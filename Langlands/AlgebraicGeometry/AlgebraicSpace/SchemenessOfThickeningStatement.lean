import Langlands.AlgebraicGeometry.AlgebraicSpace.Thickening

/-! # Schemeness of algebraic spaces under arbitrary thickenings

Stacks Project Lemma 76.9.5 (Tag 05ZR): a thickening of an algebraic space represented
by a scheme is itself represented by a scheme. The thickening has no order bound.
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- If `i : X ⟶ X'` is an arbitrary thickening of algebraic spaces over `S` and `X` is
represented by a scheme over `S`, then so is `X'`. -/
def SchemenessOfThickeningStatement : Prop :=
  ∀ (S : Scheme.{u}) (X X' : AlgebraicSpace S) (i : X ⟶ X'),
    IsThickening (hom i) →
      IsRepresentedByScheme X → IsRepresentedByScheme X'

end Langlands.AlgebraicGeometry.AlgebraicSpace
