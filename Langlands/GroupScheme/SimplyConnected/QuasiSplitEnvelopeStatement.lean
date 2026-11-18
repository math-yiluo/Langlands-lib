import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Reductive.QuasiSplit

/-! # A simply connected quasi-split subgroup containing a maximal split torus -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A simply connected semisimple group over a field has a closed simply connected
quasi-split subgroup containing the chosen maximal split torus. This is the
existence consequence of Borel–Tits (1965), Theorem 7.2, and Humphreys's
corollary in Borel–Tits (1972), 4.6. -/
def SimplyConnectedQuasiSplitEnvelopeStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSimplyConnected G →
      ∀ (S : CommGroupScheme (Spec (CommRingCat.of k))) (i : S.toGrp ⟶ G),
        IsMaximalSplitTorus i →
          ∃ (H : GroupScheme (Spec (CommRingCat.of k))) (j : H ⟶ G)
            (f : S.toGrp ⟶ H),
            IsSimplyConnected H ∧ IsQuasiSplit H ∧ IsClosedSubgroup j ∧
              IsMaximalSplitTorus f ∧ f ≫ j = i

end Langlands.GroupScheme
