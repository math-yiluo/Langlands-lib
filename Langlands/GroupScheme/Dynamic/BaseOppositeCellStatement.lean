import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Langlands.GroupScheme.Torus.Lattice

/-! # Statement: the opposite dynamic open cell over any base scheme -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The opposite dynamic open cell over any base scheme** (Conrad, *Reductive group
schemes*, Theorem 4.1.7(4) and the paragraph after Example 4.1.9). For a smooth affine
`S`-group and a cocharacter `χ`, multiplication from any representatives of `U_G(-χ)`
and `P_G(χ)` is an open immersion. Here `-χ` means precomposition with inversion
of `G_m`. -/
def DynamicBaseOppositeCellStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (χ : (Gm S).toGrp ⟶ G) (U P : GroupScheme S) (iU : U ⟶ G) (iP : P ⟶ G),
    (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom S (-1)) ≫ χ)).IsRepresentedBy iU →
    (Dynamic.parabolic χ).IsRepresentedBy iP →
      IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iP).left

end Langlands.GroupScheme
