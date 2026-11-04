import Langlands.GroupScheme.Torus.Maximal
import Langlands.GroupScheme.InnerAutomorphism

/-! # Statement: density of conjugators onto ground-field maximal tori -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Let `G` be a smooth connected affine group over an infinite field `k`, `j₀ : T₀ ⟶ G` a
maximal `k`-torus and `K` the algebraic closure of `k`. The `K`-points `g` of `G_K` that
conjugate `(T₀)_K` onto the base change of some closed `k`-torus of `G` have Zariski-dense
union of images in the underlying space of `G_K`. This is the density of the `k`-points of
the variety of maximal tori `G/N_G(T₀)`, pulled back to `G_K`. -/
def RationalMaximalTorusConjugateDensityStatement : Prop :=
  ∀ (k : Type u) [Field k] [Infinite k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (T₀ : CommGroupScheme (Spec (CommRingCat.of k))) (j₀ : T₀.toGrp ⟶ G),
    IsMaximalTorus j₀ →
      Dense (⋃ (g : Over.mk (𝟙 (Spec (CommRingCat.of (AlgebraicClosure k)))) ⟶
          ((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).X)
          (_ : ∃ (T : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G),
            IsTorus T.toGrp ∧ IsClosedSubgroup j ∧
              SubgroupFunctor.range ((GroupScheme.baseChange (toAlgebraicClosure k)).map j₀ ≫
                  (((GroupScheme.baseChange (toAlgebraicClosure k)).obj G).innerIso g).hom) =
                SubgroupFunctor.range ((GroupScheme.baseChange (toAlgebraicClosure k)).map j)),
          Set.range g.left)

end Langlands.GroupScheme
