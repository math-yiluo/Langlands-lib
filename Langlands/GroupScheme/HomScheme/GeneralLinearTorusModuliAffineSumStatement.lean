import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Langlands.GroupScheme.GeneralLinear

/-! # Statement: the moduli of subtori of `GL_n` is a sum of affine schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TorusSubgroupModuli

/-- **The scheme of subtori of `GL_n` is a sum of affine schemes** (SGA 3,
Exposé XI, Remarque 4.6, for the open and closed part of subtori).

Let `R` be a commutative ring and `n` a finite index type. Suppose that
`j : K ⟶ (GroupScheme.baseChange M.hom).obj (GeneralLinear.groupScheme n R)` is a
universal family of closed relative subtori of `GL_n` over `Spec R`, parametrized
by `M : Over (Spec R)`. Then the scheme `M.left` is the union of a family of
pairwise disjoint affine open subschemes. -/
def GeneralLinearAffineSumStatement : Prop :=
  ∀ (R : CommRingCat.{u}) (n : Type) [Fintype n] [DecidableEq n]
    (M : Over (Spec R)) (K : GroupScheme M.left)
    (j : K ⟶ (GroupScheme.baseChange M.hom).obj (GeneralLinear.groupScheme n R)),
    IsClosedSubgroup j → RelativeTorus.IsTorus K → IsUniversal j →
    ∃ (ι : Type u) (U : ι → M.left.Opens),
      (∀ k, IsAffineOpen (U k)) ∧ Pairwise (Function.onFun Disjoint U) ∧ iSup U = ⊤

end Langlands.GroupScheme.TorusSubgroupModuli
