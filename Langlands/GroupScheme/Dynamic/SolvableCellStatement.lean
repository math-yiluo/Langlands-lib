import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Langlands.GroupScheme.Absolute.Borel
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # The dynamic cell of a smooth connected solvable group is the whole group (Milne 16.35) -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Proposition 16.35: let `G` be a smooth connected solvable affine group over a
field `k` and let `χ` be a cocharacter of `G`. For any closed-subgroup representatives
`iU : U ⟶ G` of `U_G(-χ)` and `iP : P ⟶ G` of `P_G(χ)`, multiplication
`U × P → G`, `(u, p) ↦ iU(u) iP(p)`, is an isomorphism. Here `-χ` is precomposition of `χ`
with inversion of `G_m`. -/
def SolvableDynamicCellStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left],
    IsSolvableGroupScheme G →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (U P : GroupScheme (Spec (CommRingCat.of k))) (iU : U ⟶ G) (iP : P ⟶ G),
      (Dynamic.unipotent
        (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy
        iU →
      (Dynamic.parabolic χ).IsRepresentedBy iP →
        IsIso (SubgroupFunctor.cellMultiplication iU iP)

end Langlands.GroupScheme
