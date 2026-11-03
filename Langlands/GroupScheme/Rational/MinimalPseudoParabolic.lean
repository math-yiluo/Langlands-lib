import Langlands.GroupScheme.PseudoParabolic

/-! # Minimal pseudo-parabolic subgroups over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {G P : GroupScheme (Spec (CommRingCat.of k))}

/-- A pseudo-parabolic subgroup is minimal among pseudo-parabolic subgroups
defined over the ground field. Inclusion and equality concern all scheme tests. -/
def IsMinimalPseudoParabolicSubgroup (i : P ⟶ G) : Prop :=
  IsPseudoParabolicSubgroup i ∧
    ∀ (Q : GroupScheme (Spec (CommRingCat.of k))) (j : Q ⟶ G),
      IsPseudoParabolicSubgroup j →
        SubgroupFunctor.range j ≤ SubgroupFunctor.range i →
          SubgroupFunctor.range j = SubgroupFunctor.range i

namespace IsMinimalPseudoParabolicSubgroup

variable {i : P ⟶ G}

theorem isPseudoParabolicSubgroup (hi : IsMinimalPseudoParabolicSubgroup i) :
    IsPseudoParabolicSubgroup i :=
  hi.1

theorem isClosedSubgroup (hi : IsMinimalPseudoParabolicSubgroup i) :
    IsClosedSubgroup i :=
  hi.isPseudoParabolicSubgroup.isClosedSubgroup

/-- A contained pseudo-parabolic subgroup has the same all-test image. -/
theorem range_eq_of_le (hi : IsMinimalPseudoParabolicSubgroup i)
    {Q : GroupScheme (Spec (CommRingCat.of k))} {j : Q ⟶ G}
    (hj : IsPseudoParabolicSubgroup j)
    (hle : SubgroupFunctor.range j ≤ SubgroupFunctor.range i) :
    SubgroupFunctor.range j = SubgroupFunctor.range i :=
  hi.2 Q j hj hle

end IsMinimalPseudoParabolicSubgroup

end Langlands.GroupScheme
