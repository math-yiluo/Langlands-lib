import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-! # Dense affine open subspaces of separated algebraic spaces over a field

A separated algebraic space over a field with an étale surjective atlas from an affine scheme
locally of finite type has an open subspace represented by an affine scheme whose preimage in
the atlas is dense. This combines the proofs of Stacks Project, Properties of Spaces,
Proposition 66.13.3 (Tag 06NH) and Decent Spaces, Lemma 68.10.4 (Tag 06NG, third proof).
-/

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

/-- Let `X` be an fppf sheaf over a field `k` that is an algebraic space with closed-immersion
diagonal, and let `a : U ⟶ X` be an étale surjective morphism from an affine scheme `U`
locally of finite type over `k`. Then there are an affine scheme `V` over `k` and an open
immersion `i : V ⟶ X` whose pullback `p : W ⟶ U` along `a` has dense image in `U`. -/
def SeparatedDenseAffineOpenStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : FppfSheaf (Spec (CommRingCat.of k))),
    IsAlgebraicSpace (Spec (CommRingCat.of k)) X →
    IsClosedImmersion (Limits.diag X.obj) →
    ∀ (U : Over (Spec (CommRingCat.of k)))
      (a : (schemeYoneda (Spec (CommRingCat.of k))).obj U ⟶ X.obj),
      IsEtale a → IsSurjective a → IsAffine U.left → LocallyOfFiniteType U.hom →
      ∃ (V W : Over (Spec (CommRingCat.of k)))
        (i : (schemeYoneda (Spec (CommRingCat.of k))).obj V ⟶ X.obj) (p : W ⟶ U)
        (b : (schemeYoneda (Spec (CommRingCat.of k))).obj W ⟶
          (schemeYoneda (Spec (CommRingCat.of k))).obj V),
        IsAffine V.left ∧ IsOpenImmersion i ∧
          IsPullback b ((schemeYoneda (Spec (CommRingCat.of k))).map p) i a ∧
          Dense (Set.range p.left)

end Langlands.AlgebraicGeometry.AlgebraicSpace
