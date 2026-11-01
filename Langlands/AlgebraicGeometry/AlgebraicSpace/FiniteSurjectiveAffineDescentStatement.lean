import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry

/-! # Finite-surjective descent of affineness for algebraic spaces

Stacks Project Lemma 70.15.1 (Tag 07VS): if a finite surjective morphism of algebraic
spaces has a source represented by an affine scheme, then its target is represented by
an affine scheme. No finite-presentation or other hypothesis is imposed.
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- If `f : X ⟶ Y` is a finite surjective morphism of algebraic spaces over `S` and `X` is
represented by an affine scheme, then `Y` is represented by an affine scheme. -/
def FiniteSurjectiveAffineDescentStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y),
    IsFinite (hom f) → IsSurjective (hom f) →
      IsRepresentedByAffineScheme X → IsRepresentedByAffineScheme Y

end Langlands.AlgebraicGeometry.AlgebraicSpace
