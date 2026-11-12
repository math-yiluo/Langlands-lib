import Langlands.GroupScheme.Rational.MaximalLeviParabolicCountStatement
import Langlands.GroupScheme.Rational.ParabolicConjugacyTransport

/-! # A finite separated family of parabolics with a maximal Levi -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A maximal embedded Levi has a family of at most two pairwise nonconjugate
actual parabolics which covers every parabolic with a conjugate embedded Levi.
Each selected parabolic has the original Levi and a matching geometric radical. -/
def MaximalLeviParabolicFamilyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l → ¬ IsIso p →
      (∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
        IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q') →
      ∃ (n : ℕ), n ≤ 2 ∧
      ∃ (Q U : Fin n → GroupScheme (Spec (CommRingCat.of k)))
        (q : ∀ a, Q a ⟶ G) (lQ : ∀ a, M ⟶ Q a) (rQ : ∀ a, U a ⟶ Q a),
        (∀ a, IsParabolicSubgroup (q a)) ∧
        (∀ a, IsRationalLeviSubgroup (lQ a)) ∧
        (∀ a, LeviSubgroup.IsGeometricUnipotentRadical (rQ a)) ∧
        (∀ a, IsIso (subgroupMultiplication (lQ a) (rQ a))) ∧
        (∀ a, lQ a ≫ q a = l ≫ p) ∧
        (∀ a b, (SubgroupFunctor.range (q a)).IsRationallyConjugate
          (SubgroupFunctor.range (q b)) → a = b) ∧
        (∀ (Q' L' : GroupScheme (Spec (CommRingCat.of k)))
          (q' : Q' ⟶ G) (l' : L' ⟶ Q'),
          IsParabolicSubgroup q' → IsRationalLeviSubgroup l' →
          ∀ (e : M ≅ L') (g : rationalPoints G),
            e.hom ≫ l' ≫ q' = l ≫ p ≫ (G.innerIso g).hom →
            ∃ a, (SubgroupFunctor.range q').IsRationallyConjugate
              (SubgroupFunctor.range (q a)))

end Langlands.GroupScheme
