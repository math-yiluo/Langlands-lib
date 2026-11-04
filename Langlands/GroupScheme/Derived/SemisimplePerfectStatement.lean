import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Statement: semisimple field groups are perfect -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The scheme-theoretic derived subgroup functor of every semisimple field group is the
total subgroup functor. -/
def SemisimplePerfectStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G → derivedSubgroup G = ⊤

end Langlands.GroupScheme
