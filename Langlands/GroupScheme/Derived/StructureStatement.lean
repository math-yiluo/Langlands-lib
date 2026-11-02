import Langlands.GroupScheme.Derived.Basic

/-! # Structure statements for the scheme-theoretic derived subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every affine locally finite type group over any field has an actual affine locally finite
type closed subgroup representing its scheme-theoretic derived subgroup. -/
def DerivedSubgroupRepresentabilityStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    ∃ (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
      IsAffineHom D.X.hom ∧ LocallyOfFiniteType D.X.hom ∧ IsDerivedSubgroup d

/-- Field extension preserves an actual derived-subgroup inclusion and identifies the
base-changed subgroup functor with the derived subgroup of the base-changed group. -/
def DerivedSubgroupFieldBaseChangeStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsDerivedSubgroup d →
      let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
      IsDerivedSubgroup ((GroupScheme.baseChange b).map d) ∧
        (derivedSubgroup G).baseChange b =
          derivedSubgroup ((GroupScheme.baseChange b).obj G)

/-- The actual derived subgroup of a smooth affine locally finite type field group is smooth. -/
def DerivedSubgroupSmoothnessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsDerivedSubgroup d → Smooth G.X.hom → Smooth D.X.hom

/-- The actual derived subgroup of a connected affine locally finite type field group is
connected, without a smoothness hypothesis. -/
def DerivedSubgroupConnectednessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (D : GroupScheme (Spec (CommRingCat.of k))) (d : D ⟶ G),
    IsDerivedSubgroup d → ConnectedSpace G.X.left → ConnectedSpace D.X.left

/-- The four unproved structure targets: closed representability, field base change,
smoothness, and connectedness. -/
def DerivedSubgroupStructureStatement : Prop :=
  DerivedSubgroupRepresentabilityStatement.{u} ∧
    DerivedSubgroupFieldBaseChangeStatement.{u} ∧
    DerivedSubgroupSmoothnessStatement.{u} ∧
    DerivedSubgroupConnectednessStatement.{u}

end Langlands.GroupScheme
