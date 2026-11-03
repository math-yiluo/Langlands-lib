import Langlands.GroupScheme.Lie.DualNumberKernel
import Langlands.GroupScheme.Reductive.Basic

/-! # Statement: a smooth closed subgroup with the full Lie algebra is everything -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Subgroups with the full Lie algebra** (Milne, *Algebraic Groups*, Proposition 10.15 with
Proposition 1.37). Let `H` be a smooth affine group scheme over a field `k` with connected
underlying space, and `j : K ⟶ H` a closed subgroup with `K` smooth over `k`. If every element of
the actual Lie algebra `lieKernel H k` is the image under `j` of an element of `lieKernel K k`,
then `j` is surjective on points over every test scheme. -/
def LieSubgroupEqualityStatement : Prop :=
  ∀ (k : Type u) [Field k] (H K : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth H.X.hom] [IsAffineHom H.X.hom] [ConnectedSpace H.X.left] [Smooth K.X.hom]
    (j : K ⟶ H), IsClosedSubgroup j →
    (∀ X : lieKernel H k, ∃ Y : lieKernel K k, Y.val ≫ j.hom.hom = X.val) →
      SubgroupFunctor.range j = ⊤

end Langlands.GroupScheme
