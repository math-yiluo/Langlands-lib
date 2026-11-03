import Langlands.GroupScheme.SimplyConnected.Basic

/-! # The universal property of a semisimple simply connected central cover -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A central isogeny from a simply connected semisimple group has a unique
factorization through every incoming semisimple central isogeny. -/
def SimplyConnectedCentralCoverUniversalProperty : Prop :=
  ∀ (k : Type u) [Field k]
    (C G : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ G),
    IsSimplyConnected C → IsSemisimple G → IsCentralIsogeny π →
      HasCentralCoverUniversalProperty π

end Langlands.GroupScheme
