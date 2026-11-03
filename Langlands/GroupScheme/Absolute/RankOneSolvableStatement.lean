import Langlands.GroupScheme.Absolute.BorelStatement

/-! # Statement: a solvable subgroup through a split maximal torus omits a root or its negative -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Rank-one obstruction for solvable subgroups** (derived from Milne, *Algebraic Groups*
(2017), Lemma 21.28, Proposition 21.29 and Theorem 21.32). Let `G` be a connected reductive group
over a field `k`, `j : T ⟶ G` a maximal torus with `T` split, and `i : H ⟶ G` a closed subgroup
with `H` smooth, connected and solvable, through which `j` factors. Then for no root `α` of `T`
in `G` do both weight spaces `𝔤_α` and `𝔤_{-α}` contain a nonzero element of the image of
`Lie(H)` in `Lie(G)`. -/
def RankOneSolvableObstructionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (j : T.toGrp ⟶ G), IsSplitTorus T.toGrp → IsMaximalTorus j →
      haveI := hG.isAffineHom
      ∀ (H : GroupScheme (Spec (CommRingCat.of k))) (i : H ⟶ G) (f : T.toGrp ⟶ H),
        IsClosedSubgroup i → Smooth H.X.hom → ConnectedSpace H.X.left →
          IsSolvableGroupScheme H → f ≫ i = j →
          ∀ α ∈ roots j, ¬ ((∃ X ∈ weightSpace j α, X ≠ 0 ∧
              ∃ Y : lieKernel H k, Y.val ≫ i.hom.hom = X.toMul.val) ∧
            (∃ X ∈ weightSpace j (-α), X ≠ 0 ∧
              ∃ Y : lieKernel H k, Y.val ≫ i.hom.hom = X.toMul.val))

end Langlands.GroupScheme
