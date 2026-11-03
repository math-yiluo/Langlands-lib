import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Torus.Maximal

/-! # Statement: simply connected central covers of split semisimple groups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Simply connected central covers of split semisimple groups** (Milne Remark 23.60, split
case; Proposition 23.29 and Theorems 23.9 and 23.55). For every field `k : Type u` and every
semisimple group scheme `G` over `Spec k` with a split maximal torus `i : T ⟶ G`, there are an
actual group scheme `C` over `Spec k` and a central isogeny `π : C ⟶ G` with `C` algebraically
simply connected. -/
def SplitSimplyConnectedCoverExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G → IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ G),
        IsSimplyConnected C ∧ IsCentralIsogeny π

end Langlands.GroupScheme
