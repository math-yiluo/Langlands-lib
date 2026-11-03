import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Statement: existence of simply connected central covers over arbitrary fields -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Existence of the simply connected central cover** (CGP, Corollary A.4.11(1), packaged
with the universal property of Milne, Proposition 18.8). For every field `k : Type u` and every
semisimple group scheme `G` over `Spec k`, there are an actual group scheme `C` over `Spec k`
and an actual homomorphism `π : C ⟶ G` satisfying `IsSimplyConnectedCover π`: `C` is
algebraically simply connected, `π` is a central isogeny, and every central isogeny onto `G`
from a semisimple group receives a unique factorization of `π`. -/
def SimplyConnectedCoverExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G →
      ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ G), IsSimplyConnectedCover π

end Langlands.GroupScheme
