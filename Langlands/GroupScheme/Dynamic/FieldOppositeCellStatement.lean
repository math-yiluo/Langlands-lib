import Langlands.GroupScheme.Dynamic.Basic
import Langlands.GroupScheme.SubgroupFunctor.CellMultiplication
import Langlands.GroupScheme.Torus.Lattice
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Statement: the opposite dynamic open cell over a field without smoothness -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The opposite dynamic open cell over a field without smoothness**
(Conrad–Gabber–Prasad, Proposition 2.1.8(3)). For an affine group scheme of finite
type over a field, multiplication from any representatives of `U_G(-χ)` and
`P_G(χ)` is an open immersion. Here `-χ` means precomposition with inversion
of `G_m`. -/
def DynamicFieldOppositeCellStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (U P : GroupScheme (Spec (CommRingCat.of k))) (iU : U ⟶ G) (iP : P ⟶ G),
    (Dynamic.unipotent
      (CommGroupScheme.groupHom (Gm.powerHom (Spec (CommRingCat.of k)) (-1)) ≫ χ)).IsRepresentedBy
      iU →
    (Dynamic.parabolic χ).IsRepresentedBy iP →
      IsOpenImmersion (SubgroupFunctor.cellMultiplication iU iP).left

end Langlands.GroupScheme
