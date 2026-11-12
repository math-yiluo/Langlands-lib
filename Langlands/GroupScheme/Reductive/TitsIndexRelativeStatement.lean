import Langlands.GroupScheme.Reductive.TitsIndex

/-! # Star invariance, relative simple roots and split rank of the actual index -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Zero-restriction simple vertices are invariant under the actual star
action of each element of the absolute Galois group. -/
def TitsIndexStarInvariantStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (a : d.Vertex),
    d.star σ a ∈ d.zeroVertices ↔ a ∈ d.zeroVertices

/-- Restriction identifies distinguished star orbits with the existing actual
simple relative roots. The equivalence is constrained on every orbit class
by literal equality of characters of the maximal split torus. -/
def TitsIndexRelativeSimpleRootsStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    (∀ a b : d.distinguishedVertices,
      d.rootRestriction a.val.val = d.rootRestriction b.val.val ↔
        ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
          d.star σ a.val = b.val) ∧
    ∃ e : d.DistinguishedOrbit ≃
        simpleRelativeRoots d.splitInclusion d.positiveCocharacter,
      ∀ a : d.distinguishedVertices,
        (e (d.orbitClass a)).val = d.rootRestriction a.val.val

/-- The finite number of distinguished star orbits and the number of actual
simple relative roots compute the independently defined `ℕ∞` split rank. -/
def TitsIndexSplitRankStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G),
    (Nat.card d.DistinguishedOrbit : ℕ∞) = splitRank G ∧
    (Nat.card (simpleRelativeRoots d.splitInclusion d.positiveCocharacter) : ℕ∞) =
      splitRank G

/-- The star and root-comparison assertions, grouped as one focused target. -/
def TitsIndexStarRelativeRootsStatement : Prop :=
  TitsIndexStarInvariantStatement.{u} ∧ TitsIndexRelativeSimpleRootsStatement.{u}

/-- The complete relative-structure interface, without an assumed proof. -/
def TitsIndexRelativeStructureStatement : Prop :=
  TitsIndexStarRelativeRootsStatement.{u} ∧ TitsIndexSplitRankStatement.{u}

end Langlands.GroupScheme
