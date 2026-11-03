import Langlands.GroupScheme.Absolute.Borel
import Langlands.GroupScheme.Dynamic.Basic

/-! # Statement: split parabolics containing a fixed maximal torus are dynamic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Split parabolic classification with a fixed torus** (derived from Milne,
Theorem 21.91 and Corollary 21.92, with the reductive reduction at the start
of Section 21.i). Every geometric parabolic containing a split maximal torus
is the dynamic subgroup of a cocharacter of that same torus. -/
def SplitParabolicCocharacterStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
        IsSplitTorus T.toGrp → IsMaximalTorus j →
          ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G)
            (f : T.toGrp ⟶ P), IsParabolicSubgroup i → f ≫ i = j →
              ∃ nu : cocharacterLattice T,
                SubgroupFunctor.range i =
                  Dynamic.parabolic (CommGroupScheme.groupHom nu ≫ j)

end Langlands.GroupScheme
