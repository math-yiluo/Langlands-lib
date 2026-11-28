import Langlands.GroupScheme.Rational.SemistandardWeylTransporters
import Mathlib.GroupTheory.DoubleCoset

/-! # Double cosets for parabolics containing the same maximal split torus -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For two semistandard parabolics of a connected reductive group with respect to
the same maximal split torus, their rational double cosets correspond to the
relative Weyl double cosets of their distinguished Levi factors. The
correspondence is induced by the same normalizer point on both sides. -/
def SemistandardParabolicDoubleCosetStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
      IsMaximalSplitTorus i →
      ∀ (p q : SemistandardSpectralIndex i),
        let Wp := semistandardLeviRelativeWeylSubgroup i p.toLevi
        let Wq := semistandardLeviRelativeWeylSubgroup i q.toLevi
        let P := p.parabolic.rationalPoints
        let Q := q.parabolic.rationalPoints
        ∃ e : DoubleCoset.Quotient (↑Wp : Set (relativeWeylGroup i)) ↑Wq ≃
            DoubleCoset.Quotient (↑P : Set (rationalPoints G)) ↑Q,
          ∀ n : normalizerPoints i,
            e (DoubleCoset.mk Wp Wq (QuotientGroup.mk n)) =
              DoubleCoset.mk P Q (n : rationalPoints G)

end Langlands.GroupScheme
