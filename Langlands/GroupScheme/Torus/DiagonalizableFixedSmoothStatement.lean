import Langlands.GroupScheme.AutomorphicAction
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.GroupTheory.Finiteness

/-! # Smooth fixed subgroups for diagonalizable actions -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Diagonalizable

/-- A closed representative of the all-refinement fixed subgroup of a
finite-type diagonalizable action on a smooth affine group is smooth.
The character group may have torsion, including torsion in the characteristic. -/
def FixedSubgroupSmoothStatement : Prop :=
  ∀ (k : Type u) [Field k] (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    Smooth G.X.hom → IsAffineHom G.X.hom →
    ∀ (a : AutomorphicAction (groupScheme (CommRingCat.of k) Λ).toGrp G)
      (C : GroupScheme (Spec (CommRingCat.of k))) (j : C ⟶ G),
      a.fixedSubgroup.IsRepresentedBy j → IsClosedSubgroup j → Smooth C.X.hom

end Langlands.GroupScheme.Diagonalizable
