import Langlands.GroupScheme.Reductive.Semisimple
import Langlands.GroupScheme.AffineWeilRestriction

/-! # Statement: homomorphisms with commutative image from a semisimple Weil restriction -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Homomorphisms with commutative image from a semisimple Weil restriction are trivial.**
Let `B` be a finite, projective, étale `A`-algebra and `G'` a reductive group scheme over
`Spec B` whose geometric fibres are semisimple. Let `T` be an `A`-algebra, `M` a group scheme
over `Spec A`, and `c` a homomorphism from the group functor of `H = R_{B/A}(G')` on
`T`-algebras to the group functor of `M` on `T`-algebras whose values over each `T`-algebra
commute with each other. Then `c` is trivial. -/
def WeilAbelianImageTrivialityStatement : Prop :=
  ∀ (A B : Type u) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [Module.Projective A B] [Algebra.Etale A B]
    (G' : GroupScheme (Spec (CommRingCat.of B))) [IsAffine G'.X.left]
    [LocallyOfFiniteType G'.X.hom],
    IsReductive G' →
    (∀ s' : Spec (CommRingCat.of B), IsSemisimple (geometricFiber G' s')) →
    ∀ (M : GroupScheme (Spec (CommRingCat.of A))) (T : CommAlgCat.{u} (CommRingCat.of A))
      (c : Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor ⟶
        Under.forget T ⋙ M.affinePointFunctor),
      (∀ (X : Under T)
        (x y : (Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor).obj X),
        Commute (c.app X x) (c.app X y)) →
      ∀ (X : Under T)
        (x : (Under.forget T ⋙ (AffineWeil.groupScheme A B G').affinePointFunctor).obj X),
        c.app X x = 1

end Langlands.GroupScheme
