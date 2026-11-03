import Langlands.GroupScheme.SimplyConnected.DerivedCover

/-! # Statement: existence of simply connected covers of actual reductive derived subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every connected reductive field group has an actual derived-subgroup inclusion together
with an actual simply connected central cover of that derived subgroup. -/
def SimplyConnectedDerivedCoverExistenceStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ∃ (D C : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G) (π : C ⟶ D),
        IsSimplyConnectedDerivedCover d π

end Langlands.GroupScheme
