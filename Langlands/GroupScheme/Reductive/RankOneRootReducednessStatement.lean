import Langlands.GroupScheme.Reductive.RootDatum

/-! # Statement: reducedness of the roots when all roots are proportional (semisimple rank one) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Reducedness of the roots in semisimple rank one** (the case `G = G_α` of Milne,
Theorem 21.11(b)). Let `G` be a connected reductive group over a field with a split maximal torus
`i : T ⟶ G`, and suppose that any two roots of `i` are linearly dependent over `ℤ` in the
character lattice. Then any two roots of `i` are equal or opposite. -/
def RankOneRootReducednessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      (∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β]) →
        ∀ α ∈ roots i, ∀ β ∈ roots i, α = β ∨ α = -β

end Langlands.GroupScheme
