import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! # The universal closed-factorization locus -/

universe u

open CategoryTheory CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

/-- The coordinate module becomes projective over some faithfully flat base
extension. Affineness and flatness of the structural morphism are separate. -/
def HasFpqcProjectiveCoordinateModule {R : CommRingCat.{u}}
    (X : Over (Spec R)) : Prop :=
  ∃ B : CommAlgCat.{u} R, Module.FaithfullyFlat R B ∧
    Module.Projective B (B ⊗[R] ((algΓ R).obj X).unop)

/-- The generic closed-subfunctor construction extracted from CGP A.8.10(1):
maps to `Y` whose entire product with `X` factors through `D` form a closed locus. -/
def ClosedFactorizationLocusStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (X : Over (Spec R)),
    IsAffineHom X.hom → Flat X.hom → HasFpqcProjectiveCoordinateModule X →
    ∀ (Y D : Over (Spec R)) (d : D ⟶ X ⊗ Y), IsClosedImmersion d.left →
      ∃ (Z : Over (Spec R)) (i : Z ⟶ Y), IsClosedImmersion i.left ∧
        ∀ (T : Over (Spec R)) (t : T ⟶ Y),
          (∃ z : T ⟶ Z, z ≫ i = t) ↔
            ∃ q : X ⊗ T ⟶ D, q ≫ d = (X ◁ t)

end Langlands.AlgebraicGeometry
