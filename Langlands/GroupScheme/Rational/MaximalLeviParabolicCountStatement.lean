import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Reductive.Basic

/-! # At most two rational parabolics have a specified maximal Levi -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The upper-bound part of Renard V.4.8 in terms of actual subgroup images:
a finite family of distinct rational parabolics with the same embedded maximal
Levi has at most two members. -/
def MaximalLeviParabolicCountStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P M : GroupScheme (Spec (CommRingCat.of k))) (p : P ⟶ G) (l : M ⟶ P),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l → ¬ IsIso p →
      (∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
        IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q') →
      ∀ (n : ℕ) (Q : Fin n → GroupScheme (Spec (CommRingCat.of k)))
        (q : ∀ i, Q i ⟶ G) (lQ : ∀ i, M ⟶ Q i),
        (∀ i, IsParabolicSubgroup (q i)) →
        (∀ i, IsRationalLeviSubgroup (lQ i)) →
        (∀ i, lQ i ≫ q i = l ≫ p) →
        Function.Injective (fun i => SubgroupFunctor.range (q i)) → n ≤ 2

end Langlands.GroupScheme
