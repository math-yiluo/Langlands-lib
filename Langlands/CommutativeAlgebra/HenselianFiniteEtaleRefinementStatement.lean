import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Finiteness.Defs

/-! # Statement: finite étale local refinement over a Henselian local ring -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.CommutativeAlgebra

/-- An affine étale neighbourhood meeting the closed point of a Henselian local
base admits a refinement by the spectrum of a local finite étale algebra.
This is a scheme-theoretic consequence of Stacks Project, Tags 04GG and 04GH. -/
def HenselianFiniteEtaleRefinementStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [HenselianLocalRing R]
    (A : Type u) [CommRing A]
    (f : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R)),
    Etale f → IsLocalRing.closedPoint R ∈ Set.range f →
    ∃ (R' : Type u) (_ : CommRing R') (_ : IsLocalRing R') (_ : Algebra R R'),
      Algebra.Etale R R' ∧ Module.Finite R R' ∧
      ∃ g : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of A),
        g ≫ f = Spec.algebraMap R R'

end Langlands.CommutativeAlgebra
