import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.AffineWeilRestriction

/-! # Statement: normal idempotent endomorphisms of a Weil restriction of almost simple groups -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj TensorProduct

namespace Langlands.GroupScheme

/-- **Normal idempotent endomorphisms of `R_{B/A}(G')` are the factor projections.**
Let `B` be a finite, projective, étale `A`-algebra and `G'` a reductive group scheme over
`Spec B` whose geometric fibres are almost simple. Let `T` be an `A`-algebra and `ψ` an
endomorphism of the group functor of `H = R_{B/A}(G')` on `T`-algebras that is idempotent
(`ψ ∘ ψ = ψ`) and normal (`ψ (h x h⁻¹) = h ψ(x) h⁻¹`). Then there is exactly one idempotent
`e` of `B ⊗_A T` such that, for every `T`-algebra `X`, with `e'` the image of `e` in
`B ⊗_A X`, the point `ψ(x) ∈ H(X) = G'(B ⊗_A X)` agrees with `x` on the factor
`(B ⊗_A X)/(1 - e')` and is trivial on the factor `(B ⊗_A X)/(e')`. -/
def WeilFactorIdempotentRigidityStatement : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.Projective A B] [Algebra.Etale A B]
    (G' : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G'.X.left]
    [LocallyOfFiniteType G'.X.hom],
    IsReductive G' →
    (∀ s' : Spec (CommRingCat.of B), IsAlmostSimple (geometricFiber G' s')) →
    ∀ (T : CommAlgCat.{u} (CommRingCat.of A))
      (ψ : Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor ⟶
        Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor),
      ψ ≫ ψ = ψ →
      (∀ (X : Under T)
        (h x : (Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor).obj X),
        ψ.app X (h * x * h⁻¹) = h * ψ.app X x * h⁻¹) →
      ∃! e : B ⊗[A] T, IsIdempotentElem e ∧
        ∀ (X : Under T) (x : (AffineWeil.groupScheme A B G').affinePoints X.right),
          G'.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ B
              (Ideal.span {1 - Algebra.TensorProduct.lTensor (S := B) B X.hom.hom e})))
              (AffineWeil.pointsEquiv A B G' X.right (ψ.app X x)) =
            G'.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ B
              (Ideal.span {1 - Algebra.TensorProduct.lTensor (S := B) B X.hom.hom e})))
              (AffineWeil.pointsEquiv A B G' X.right x) ∧
          G'.affinePointMap (CommAlgCat.ofHom (Ideal.Quotient.mkₐ B
              (Ideal.span {Algebra.TensorProduct.lTensor (S := B) B X.hom.hom e})))
              (AffineWeil.pointsEquiv A B G' X.right (ψ.app X x)) = 1

end Langlands.GroupScheme
