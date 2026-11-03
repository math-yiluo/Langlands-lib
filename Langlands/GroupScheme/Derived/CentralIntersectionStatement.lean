import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Dynamic.Functoriality
import Langlands.GroupScheme.Rational.Characters
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finiteness of the full central intersection with an actual derived subgroup -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- For every actual derived-subgroup inclusion of a connected reductive field group,
the inverse image of the full scheme-theoretic centre has a finite closed representative. -/
def DerivedCentralIntersectionFinitenessStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsConnectedReductive G → IsDerivedSubgroup d →
      ∃ (C : GroupScheme (Spec (CommRingCat.of k))) (c : C ⟶ D),
        IsClosedSubgroup c ∧
          SubgroupFunctor.range c = (center G).comap d ∧ IsFinite C.X.hom

end Langlands.GroupScheme
