import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.AffinePoints

/-! # Statement: normal idempotent endomorphisms of a group with almost simple geometric fibres,
over any base -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Normal idempotent endomorphisms of a group with almost simple geometric fibres.**
Let `G` be a reductive group scheme over `Spec B` whose geometric fibres are almost simple.
Let `T` be a `B`-algebra and `θ` an endomorphism of the group functor of `G` on `T`-algebras
that is idempotent (`θ ∘ θ = θ`) and normal (`θ (h x h⁻¹) = h θ(x) h⁻¹`). Then there is
exactly one idempotent `e` of `T` such that, for every `T`-algebra `X`, with `e'` the image of
`e` in `X`, the point `θ(x) ∈ G(X)` agrees with `x` on the factor `X/(1 - e')` and is trivial
on the factor `X/(e')`. So `θ` is the identity over `Spec (T e)` and trivial over
`Spec (T (1 - e))`. -/
def RelativeAlmostSimpleNormalIdempotentStatement : Prop :=
  ∀ (B : Type u) [CommRing B] (G : GroupScheme (Spec (CommRingCat.of B))),
    IsReductive G →
    (∀ s : Spec (CommRingCat.of B), IsAlmostSimple (geometricFiber G s)) →
    ∀ (T : CommAlgCat.{u} (CommRingCat.of B))
      (θ : Under.forget T ⋙ G.affinePointFunctor ⟶ Under.forget T ⋙ G.affinePointFunctor),
      θ ≫ θ = θ →
      (∀ (X : Under T) (h x : (Under.forget T ⋙ G.affinePointFunctor).obj X),
        θ.app X (h * x * h⁻¹) = h * θ.app X x * h⁻¹) →
      ∃! e : T, IsIdempotentElem e ∧
        ∀ (X : Under T) (x : G.affinePoints X.right),
          G.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ B
              (Ideal.span {1 - X.hom.hom e}))) (θ.app X x) =
            G.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ B
              (Ideal.span {1 - X.hom.hom e}))) x ∧
          G.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ B
              (Ideal.span {X.hom.hom e}))) (θ.app X x) = 1

end Langlands.GroupScheme
