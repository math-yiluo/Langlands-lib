import Langlands.Representation.Exponents.ArbitraryParabolicLeviPoints
import Langlands.GroupScheme.Reductive.Basic

/-! # Actual nested-parabolic extension through a rational Levi

Derived geometric packaging of Borel--Tits 1965, Proposition 4.4(c),
with the supplied rational Levi decompositions retained. This is a proposition
only; it supplies no proof or representation-theoretic transitivity.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

open GroupScheme

/-- An inner actual parabolic of a supplied actual Levi extends to an ambient
parabolic with the same original inner Levi and exact all-test intersection. -/
def LeviParabolicExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (_hG : IsConnectedReductive G)
    (P M U : GroupScheme (Spec (CommRingCat.of k)))
    (p : P ⟶ G) (l : M ⟶ P) (r : U ⟶ P)
    (_hp : IsParabolicSubgroup p) (_hl : IsRationalLeviSubgroup l)
    (_hr : LeviSubgroup.IsGeometricUnipotentRadical r)
    (_hmul : IsIso (subgroupMultiplication l r))
    (Q N V : GroupScheme (Spec (CommRingCat.of k)))
    (q : Q ⟶ M) (n : N ⟶ Q) (s : V ⟶ Q)
    (_hq : IsParabolicSubgroup q) (_hn : IsRationalLeviSubgroup n)
    (_hs : LeviSubgroup.IsGeometricUnipotentRadical s)
    (_hmulQ : IsIso (subgroupMultiplication n s)),
    ∃ (R W : GroupScheme (Spec (CommRingCat.of k)))
      (pR : R ⟶ G) (nR : N ⟶ R) (rR : W ⟶ R)
      (_hpR : IsParabolicSubgroup pR) (_hnR : IsRationalLeviSubgroup nR)
      (_hrR : LeviSubgroup.IsGeometricUnipotentRadical rR)
      (_hmulR : IsIso (subgroupMultiplication nR rR)),
      nR ≫ pR = n ≫ q ≫ l ≫ p ∧
      SubgroupFunctor.range pR ≤ SubgroupFunctor.range p ∧
      SubgroupFunctor.range (q ≫ l ≫ p) =
        SubgroupFunctor.range (l ≫ p) ⊓ SubgroupFunctor.range pR

end Langlands.Aubert.General.RepresentedParabolic
