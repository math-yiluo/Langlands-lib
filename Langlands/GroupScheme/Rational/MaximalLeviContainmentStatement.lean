import Langlands.GroupScheme.Rational.LeviSubgroup
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Absolute.Borel

/-! # Levi subgroups of proper parabolics containing a maximal Levi

In the proof of Renard VII.1.3 (PDF p.230) the geometric lemma VI.5.3 leaves only the
contributions of the parabolics whose Levi factor is conjugate to the maximal Levi `M`. The
structural input is that the Levi `L` of a proper parabolic `Q` cannot strictly contain a
maximal Levi `M`: `A_L ⊆ A_M`, `A_M / A_G` has dimension one, and `Q ≠ G` forces
`A_L ≠ A_G`, so `A_L = A_M` and `L = Z_G(A_L) = M`. This module states that input for
actual rational parabolics and Levi subgroups, as an equality of subgroup functors.
Nothing is proved here.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `P = MN` be an actual maximal proper rational parabolic of a connected reductive
group `G`, with rational Levi `M`. If the rational Levi `L` of an actual proper rational
parabolic `Q` of `G` contains `M`, as subgroup functors of `G`, then `L = M`. Maximality
means that every rational parabolic through which `p` factors is `P` itself or `G`. -/
def MaximalLeviContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (P M Q L : GroupScheme (Spec (CommRingCat.of k)))
      (p : P ⟶ G) (l : M ⟶ P) (q : Q ⟶ G) (lQ : L ⟶ Q),
      IsParabolicSubgroup p → IsRationalLeviSubgroup l → ¬ IsIso p →
      (∀ (Q' : GroupScheme (Spec (CommRingCat.of k))) (q' : Q' ⟶ G) (j : P ⟶ Q'),
        IsParabolicSubgroup q' → j ≫ q' = p → IsIso j ∨ IsIso q') →
      IsParabolicSubgroup q → IsRationalLeviSubgroup lQ → ¬ IsIso q →
      SubgroupFunctor.range (l ≫ p) ≤ SubgroupFunctor.range (lQ ≫ q) →
        SubgroupFunctor.range (l ≫ p) = SubgroupFunctor.range (lQ ≫ q)

end Langlands.GroupScheme
