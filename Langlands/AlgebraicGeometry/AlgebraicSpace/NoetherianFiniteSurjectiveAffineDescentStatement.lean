import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry

/-! # Noetherian finite-surjective descent of affineness

Statement of Stacks Project Lemma 69.17.3 (Tag 07VP), using a Noetherian
étale-surjective scheme chart of the target. The paired Markdown explains why
the other hypotheses supply the quasi-separatedness in Stacks' convention.
-/

universe u

open CategoryTheory
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- A finite surjective morphism from an affine algebraic space to one admitting
a Noetherian étale-surjective scheme chart has an affine target. -/
def NoetherianFiniteSurjectiveAffineDescentStatement : Prop :=
  ∀ (S : Scheme.{u}) (X Y : AlgebraicSpace S) (f : X ⟶ Y),
    IsFinite (hom f) → IsSurjective (hom f) →
      IsRepresentedByAffineScheme X →
      (∃ (U : Over S) (a : (schemeYoneda S).obj U ⟶ Y.presheaf),
          IsEtale a ∧ IsSurjective a ∧ IsNoetherian U.left) →
      IsRepresentedByAffineScheme Y

end Langlands.AlgebraicGeometry.AlgebraicSpace
