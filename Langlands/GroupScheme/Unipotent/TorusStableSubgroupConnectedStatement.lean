import Langlands.GroupScheme.RepresentedAction
import Langlands.GroupScheme.Torus.Lattice
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Torus-stable subgroups of connected unipotent groups (Milne 16.25) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.25: let `U` be a connected unipotent affine algebraic group over a
field `k` and let a torus `T` act on `U` by group automorphisms (`a : AutomorphicAction T U`).
Every closed subgroup `H` of `U` that is stable under `T` and contains the fixed subgroup `U^T`
is connected. In particular, every closed subgroup representing `U^T` is connected. -/
def TorusStableUnipotentSubgroupConnectedStatement : Prop :=
  ∀ (k : Type u) [Field k] (U T : GroupScheme (Spec (CommRingCat.of k)))
    [LocallyOfFiniteType U.X.hom] [IsAffineHom U.X.hom],
    ConnectedSpace U.X.left → IsUnipotent U → IsTorus T →
    ∀ a : AutomorphicAction T U,
      (∀ (H : GroupScheme (Spec (CommRingCat.of k))) (h : H ⟶ U),
        IsClosedSubgroup h → a.IsStable (SubgroupFunctor.range h) →
          a.fixedSubgroup ≤ SubgroupFunctor.range h → ConnectedSpace H.X.left) ∧
      ∀ (F : GroupScheme (Spec (CommRingCat.of k))) (j : F ⟶ U),
        IsClosedSubgroup j → SubgroupFunctor.range j = a.fixedSubgroup →
          ConnectedSpace F.X.left

end Langlands.GroupScheme
