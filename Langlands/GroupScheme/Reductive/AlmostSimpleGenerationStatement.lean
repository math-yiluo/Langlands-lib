import Langlands.GroupScheme.Reductive.AlmostSimple

/-! # Generation of semisimple groups by normal almost-simple subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A closed subgroup of a semisimple group over an algebraically closed field
which contains every normal almost-simple subgroup is the whole group. This
is the generation consequence of the first assertion of Milne 21.51. -/
def SemisimpleAlmostSimpleGenerationStatement : Prop :=
  ∀ (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))), IsSemisimple G →
    ∀ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
      IsClosedSubgroup d →
      (∀ (A : GroupScheme (Spec (CommRingCat.of k))) (a : A ⟶ G),
        IsAlmostSimple A → IsClosedSubgroup a →
        (SubgroupFunctor.range a).IsNormal →
        SubgroupFunctor.range a ≤ SubgroupFunctor.range d) →
      SubgroupFunctor.range d = ⊤

end Langlands.GroupScheme
