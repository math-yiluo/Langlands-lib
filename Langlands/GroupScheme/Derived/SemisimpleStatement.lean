import Langlands.GroupScheme.Derived.Basic
import Langlands.GroupScheme.Reductive.Semisimple

/-! # Statement: actual derived subgroups of connected reductive groups are semisimple -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual inclusion exhibiting the scheme-theoretic derived subgroup of a connected
reductive field group has a semisimple source. -/
def DerivedSubgroupSemisimpleStatement : Prop :=
  ∀ (k : Type u) [Field k] (G D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsConnectedReductive G → IsDerivedSubgroup d → IsSemisimple D

end Langlands.GroupScheme
