import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexStatement
import Langlands.GroupScheme.Quaternionic.GroupSchemes
import Langlands.GroupScheme.SimplyConnected.SpinCoverFundamentalWeight

/-!
# Index comparisons for an aligned spin cover

This unproved prerequisite reads the split rank and the nonfork distinguished
vertices of a numbered type-`D` index from any spin presentation over a central
division algebra whose vector vertex is the vertex numbered `0`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Let `G` be simply connected and absolutely almost simple with a numbered
type-`D_n` index (`n ≥ 4`) whose full star action fixes the nonfork vertices.
For every spin cover `π : G ⟶ O(q)` of a nondegenerate `σ`-quadratic form `q`
on `D^m`, with `D` central division of degree `degree`, `m * degree = 2 * n`
and `σ` of Tits type 1, such that the fundamental weight at the vertex numbered
`0` is trivial on `ker π` in the pinning torus over `K^s`, the Witt index of `q`
is the split rank of `G`, and a nonfork vertex is distinguished exactly when its
one-based number is a positive multiple `j * degree` with `j` at most the Witt
index.

This is an unproved general index-comparison prerequisite. -/
def AlignedSpinCoverTitsIndexStatement : Prop :=
  ∀ (K : Type u) [Field K]
    (G : GroupScheme (Spec (CommRingCat.of K))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)
    (n : ℕ) (e : d.Vertex ≃ Fin n),
    4 ≤ n →
    IsSimplyConnected G → IsAbsolutelyAlmostSimple G →
    (∀ a b, d.cartan a b = CartanMatrix.D n (e a) (e b)) →
    (∀ (γ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (a : d.Vertex),
      (e a).val + 2 < n → d.star γ a = a) →
    ∀ (D : Type u) [DivisionRing D] [Algebra K D]
      [Algebra.IsCentral K D] [FiniteDimensional K D]
      (degree m : ℕ),
      0 < degree → Module.finrank K D = degree ^ 2 → m * degree = 2 * n →
      ∀ σ : Quaternionic.FirstKindInvolution K D,
        Module.finrank K σ.symmetricSubspace = degree * (degree + 1) / 2 →
        ∀ q : σ.QuadraticForms (Fin m),
          σ.IsNondegenerateQuadratic q →
          ∀ π : G ⟶ σ.isometryGroup q, σ.IsSpinCover q π →
            (∀ v : d.Vertex, (e v).val = 0 → d.FundamentalWeightTrivialOnKernel v π) →
            σ.quadraticWittIndex q = splitRank G ∧
              (∀ a : d.Vertex, (e a).val + 2 < n →
                (a ∈ d.distinguishedVertices ↔
                  ∃ j : ℕ, 0 < j ∧ j ≤ σ.quadraticWittIndex q ∧
                    (e a).val + 1 = j * degree))

end Langlands.GroupScheme
