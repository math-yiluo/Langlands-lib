import Langlands.GroupScheme.SimplyConnected.Basic

/-! # Field-extension compatibility of semisimplicity, simple connectedness and covers -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Semisimplicity of an actual field group is preserved by base change along an arbitrary
field extension `k → K`. -/
def IsSemisimpleFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSemisimple G →
      IsSemisimple
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

/-- Algebraic simple connectedness of an actual field group is preserved by base change
along an arbitrary field extension `k → K`. -/
def IsSimplyConnectedFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k))),
    IsSimplyConnected G →
      IsSimplyConnected
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).obj G)

/-- Every supplied simply connected cover `π : C ⟶ G` remains one, universal property
included, after base change of the actual map along an arbitrary field extension `k → K`. -/
def IsSimplyConnectedCoverFieldExtensionStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (C G : GroupScheme (Spec (CommRingCat.of k))) (π : C ⟶ G),
    IsSimplyConnectedCover π →
      IsSimplyConnectedCover
        ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k K)))).map π)

/-- The package of the three field-extension compatibilities at universe `u`. -/
def SimplyConnectedFieldExtensionStatement : Prop :=
  IsSemisimpleFieldExtensionStatement.{u} ∧ IsSimplyConnectedFieldExtensionStatement.{u} ∧
    IsSimplyConnectedCoverFieldExtensionStatement.{u}

end Langlands.GroupScheme
