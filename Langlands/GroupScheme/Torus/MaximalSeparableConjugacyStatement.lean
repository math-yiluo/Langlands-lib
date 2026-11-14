import Langlands.GroupScheme.Torus.Maximal
import Mathlib.FieldTheory.IsSepClosed

/-! # Statement: maximal tori are conjugate over a finite separable extension -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne, Theorem 17.87 and the sentence after it. Let `G` be a smooth affine group over a
field `k`, and let `j : T ⟶ G` and `j' : T' ⟶ G` be maximal tori.
* There are a finite separable field extension `K/k` and a point `g` of `G_K` over `K` such
  that conjugation by `g` carries the base change of `T` to `K` onto that of `T'`.
* If `k` is separably closed, conjugation by some `k`-point of `G` carries `T` onto `T'`. -/
def MaximalTorusSeparableConjugacyStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (T T' : CommGroupScheme (Spec (CommRingCat.of k))) (j : T.toGrp ⟶ G)
    (j' : T'.toGrp ⟶ G), IsMaximalTorus j → IsMaximalTorus j' →
      (∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : FiniteDimensional k K)
          (_ : Algebra.IsSeparable k K),
        let b := Spec.map (CommRingCat.ofHom (algebraMap k K))
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ ((GroupScheme.baseChange b).obj G).X,
          SubgroupFunctor.range ((GroupScheme.baseChange b).map j ≫
              (((GroupScheme.baseChange b).obj G).innerIso g).hom) =
            SubgroupFunctor.range ((GroupScheme.baseChange b).map j')) ∧
      (IsSepClosed k → ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
        SubgroupFunctor.range (j ≫ (G.innerIso g).hom) = SubgroupFunctor.range j')

end Langlands.GroupScheme
