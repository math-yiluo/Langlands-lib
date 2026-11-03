import Langlands.GroupScheme.AutomorphicAction.CocycleModel
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.GroupTheory.Finiteness

/-! # Smooth action relations on diagonalizable cocycle models -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Diagonalizable

/-- The actual conjugation action relation on an affine finite-type model of
cocycles for a diagonalizable action on a smooth affine group is smooth.
Torsion in the character group is allowed in every characteristic. -/
def CocycleModelActionRelationSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (a : AutomorphicAction (groupScheme (CommRingCat.of k) Λ).toGrp G)
    (M : a.CocycleModel)
    [IsAffineHom M.scheme.hom] [LocallyOfFiniteType M.scheme.hom],
      Smooth M.actionRelation.left

end Langlands.GroupScheme.Diagonalizable
