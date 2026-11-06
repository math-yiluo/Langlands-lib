import Mathlib.GroupTheory.DoubleCoset
import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Rational.SplitTorus
import Langlands.GroupScheme.InnerAutomorphism

/-! # Finite parabolic double cosets with torus-adapted representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For actual parabolic subgroups `p : P ⟶ G` and `q : Q ⟶ G` of a connected reductive
group over a field, with rational Levi subgroups `l : M ⟶ P` and `lQ : L ⟶ Q`, the double
coset space `P(k) \ G(k) / Q(k)` of literal point images is finite, and every double coset
`P(k) g Q(k)` has a representative `z` such that some maximal split torus of `G` lies in both
`M` and `z L z⁻¹`. Containment is factorization: through `l ≫ p`, respectively through
`lQ ≫ q` followed by the inner automorphism of `z`. -/
def RepresentedParabolicDoubleCosetStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (_hG : IsConnectedReductive G)
    (P M Q L : GroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (_hp : IsParabolicSubgroup p) (_hl : IsRationalLeviSubgroup l)
    (q : Q ⟶ G) (lQ : L ⟶ Q) (_hq : IsParabolicSubgroup q) (_hlQ : IsRationalLeviSubgroup lQ),
    Finite (DoubleCoset.Quotient ((rationalPoints.map p).range : Set (rationalPoints G))
      ((rationalPoints.map q).range : Set (rationalPoints G))) ∧
    ∀ g : rationalPoints G, ∃ z : rationalPoints G,
      DoubleCoset.mk (rationalPoints.map p).range (rationalPoints.map q).range z =
        DoubleCoset.mk (rationalPoints.map p).range (rationalPoints.map q).range g ∧
      ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (i : T.toGrp ⟶ G),
        IsMaximalSplitTorus i ∧ (∃ a : T.toGrp ⟶ M, a ≫ l ≫ p = i) ∧
          ∃ b : T.toGrp ⟶ L, b ≫ lQ ≫ q ≫ (G.innerIso z).hom = i

end Langlands.GroupScheme
