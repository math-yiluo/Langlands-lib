import Langlands.GroupScheme.Lie.ConjugationDerivation
import Langlands.GroupScheme.Torus.SplitCharacterPoint
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # The coordinate algebra of a torus over the algebraic closure -/

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

universe u

/-- After base change to an algebraic closure, a torus has coordinate algebra
the group algebra of its character lattice, with monomials corresponding to
the actual characters as regular functions. -/
def GeometricTorusCoordinateAlgebraStatement : Prop :=
  ∀ (F : Type u) [Field F] (T : CommGroupScheme (Spec (CommRingCat.of F))),
    IsTorus T.toGrp →
      let K := AlgebraicClosure F
      let S := (CommGroupScheme.baseChange
        (Spec.map (CommRingCat.ofHom (algebraMap F K)))).obj T
      ∃ (_ : IsAffineHom S.toGrp.X.hom)
        (e : AddMonoidAlgebra K (characterLattice S) ≃ₐ[K] Lie.coordinateAlgebra S.toGrp),
        ∀ χ : characterLattice S,
          e (AddMonoidAlgebra.single χ 1) =
            (SplitCharacterPoint.value χ (Lie.universalPoint S.toGrp)).val

end Langlands.GroupScheme
