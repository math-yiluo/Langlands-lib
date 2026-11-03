import Langlands.GroupScheme.Reductive.RootDatum

/-! # Statement: in semisimple rank one, a cocharacter is positive on at most one root -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Uniqueness of the positive root in semisimple rank one** (Milne, Section 20e and the
proof of Theorem 21.11(b)). Let `G` be a connected reductive group over a field with a split
maximal torus `i : T ⟶ G`, and suppose that any two roots of `i` are linearly dependent over `ℤ`
in the character lattice. Then for every cocharacter `ν` of `T`, at most one root `α` of `i`
satisfies `⟨α, ν⟩ > 0`. -/
def RankOnePositiveRootUniquenessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      (∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) →
        ∀ ν : cocharacterLattice T, ∀ α ∈ roots i, ∀ β ∈ roots i,
          0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β

end Langlands.GroupScheme
