import Langlands.GroupScheme.Reductive.Basic

/-! # Connected reductivity under arbitrary field extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Arbitrary field extension preserves the existing geometric-unipotent-radical
predicate for an actual connected reductive group scheme. -/
def ConnectedReductiveFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
      IsConnectedReductive
        ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

end Langlands.GroupScheme
