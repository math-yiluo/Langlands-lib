import Langlands.GroupScheme.Reductive.RootDatum

/-! # Statement: the roots of a split maximal torus of a connected reductive group are reduced -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Reducedness of the roots** (Milne Theorem 21.11(b)). For a connected reductive group `G`
over a field with a split maximal torus `i : T ⟶ G`, two roots of `i` that are linearly dependent
over `ℤ` in the character lattice are equal or opposite. Equivalently, the only rational multiples
of a root `α` that are roots are `±α`. -/
def RootReducednessStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp → ∀ i : T.toGrp ⟶ G, IsMaximalTorus i →
      haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β] → α = β ∨ α = -β

end Langlands.GroupScheme
