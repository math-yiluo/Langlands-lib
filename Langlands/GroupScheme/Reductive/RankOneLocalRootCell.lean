import Langlands.GroupScheme.Reductive.RankOneLocalCoroot
import Langlands.GroupScheme.Reductive.SplitRankOneRootCellProof

/-! # Root-cell data from an open cell and a Weyl point

For cell data `D` on an irreducible separated group locally of finite type, a `k`-point `n`
normalizing the split torus through an automorphism negating the nonzero root `α`, and a
cocharacter `ν` whose dynamic centralizer is represented by the torus, the coroot of
`RankOneLocalCoroot.exists_coroot` and a rescaled negative root group satisfy every clause of
`RootCell.IsRootCell`. See the paired Markdown.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace RankOneLocalRootCell

open RankOneRootCellRelation

variable {k : Type u} [Field k]

/-- **Root-cell data.** Cell data with a Weyl point negating the root yields a coroot `h` with
`⟨α, h⟩ = 2` and a negative root group `xm'` such that `(xp, xm')` is a root cell for
`(α, h)`. -/
theorem exists_isRootCell (D : CellData k) [LocallyOfFiniteType D.G.X.hom]
    [IrreducibleSpace D.G.X.left] [Mono D.i.hom.hom] (hsep : IsSeparated D.G.X.hom)
    (hT : IsSplitTorus D.T.toGrp) (hα : D.α ≠ 0) {ν : cocharacterLattice D.T}
    (hC : (Dynamic.centralizer (CommGroupScheme.groupHom ν ≫ D.i)).IsRepresentedBy D.i)
    {n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ D.G.X} {σ : D.T ≅ D.T}
    (hn : IsNormalizingPoint D.i n σ) (hσ : σ.hom ≫ D.α = -D.α) :
    ∃ (h : cocharacterLattice D.T) (xm' : Ga k ⟶ D.G),
      latticePairing D.T D.α h = 2 ∧ RootCell.IsRootCell D.i D.α h D.xp xm' := by
  obtain ⟨h, pair, rfl⟩ := RankOneLocalCoroot.exists_coroot D hT hα hn hσ
  have hσ2 : (latticeReflectionIso D.α h pair).hom ≫ (latticeReflectionIso D.α h pair).hom =
      𝟙 D.T :=
    (latticeReflectionIso D.α h pair).hom_inv_id
  have hn2 := RankOneLocalCoroot.exists_sq_eq_of_involution hC hn hσ2
  let W : WeylData k :=
    { toCellData := D, h := h, pair := pair, n := n, hn := hn, hn2 := hn2,
      irreducible := inferInstance }
  exact ⟨h, W.xm', pair, W.isRootCell hsep⟩

end RankOneLocalRootCell

end Langlands.GroupScheme
