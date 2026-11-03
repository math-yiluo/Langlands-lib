import Langlands.GroupScheme.Absolute.Borel

/-! # Parabolic subgroups under arbitrary field extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Arbitrary field extension preserves an actual parabolic subgroup inclusion
in a connected reductive group, using the existing geometric Borel criterion. -/
def ParabolicFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      ∀ (P : GroupScheme (Spec (CommRingCat.of k))) (i : P ⟶ G),
        IsParabolicSubgroup i →
          IsParabolicSubgroup
            ((GroupScheme.baseChange
              (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map i)

end Langlands.GroupScheme
