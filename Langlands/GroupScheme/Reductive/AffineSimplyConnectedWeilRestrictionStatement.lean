import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.AffineWeilRestriction

/-! # Statement: simply connected semisimple group schemes as Weil restrictions -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- **Simply connected semisimple groups are Weil restrictions of absolutely simple ones**
(Conrad, *Reductive group schemes* (2014), Proposition 6.4.4, over an affine base `Spec A`).
Let `G` be a reductive group scheme over `Spec A` whose geometric fibres are simply connected
semisimple groups and nontrivial. Then there are a finite étale `A`-algebra `B` with
`Spec B → Spec A` surjective and a reductive group scheme `G'` over `Spec B` whose geometric
fibres are simply connected and almost simple, with `G ≅ R_{B/A}(G')`. Moreover the pair
`(B, G')` is unique up to isomorphism: for two such pairs `(B, G')` and `(B'', G'')` there are
an `A`-algebra isomorphism `α : B'' ≃ B` and an isomorphism from the base change of `G''` along
`Spec α` to `G'`. -/
def AffineSimplyConnectedWeilRestrictionStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (G : GroupScheme (Spec (CommRingCat.of A))),
    IsReductive G →
    (∀ s : Spec (CommRingCat.of A), IsSimplyConnected (geometricFiber G s)) →
    (∀ s : Spec (CommRingCat.of A),
      ∃ (T : Over (Spec (CommRingCat.of
          (AlgebraicClosure ((Spec (CommRingCat.of A)).residueField s)))))
        (x : T ⟶ (geometricFiber G s).X), x ≠ 1) →
    (∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
        (_ : Module.Projective A B) (_ : Algebra.Etale A B)
        (G' : GroupScheme (Spec (CommRingCat.of B)))
        (_ : IsAffine G'.X.left) (_ : LocallyOfFiniteType G'.X.hom),
        Surjective (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
        IsReductive G' ∧
        (∀ s' : Spec (CommRingCat.of B),
          IsSimplyConnected (geometricFiber G' s') ∧ IsAlmostSimple (geometricFiber G' s')) ∧
        Nonempty (G ≅ AffineWeil.groupScheme A B G')) ∧
    ∀ (B B'' : Type u) [CommRing B] [CommRing B''] [Algebra A B] [Algebra A B'']
      [Module.Finite A B] [Module.Finite A B''] [Module.Projective A B]
      [Module.Projective A B''] [Algebra.Etale A B] [Algebra.Etale A B'']
      (G' : GroupScheme (Spec (CommRingCat.of B)))
      (G'' : GroupScheme (Spec (CommRingCat.of B'')))
      [IsAffine G'.X.left] [LocallyOfFiniteType G'.X.hom]
      [IsAffine G''.X.left] [LocallyOfFiniteType G''.X.hom],
      IsReductive G' → IsReductive G'' →
      (∀ s' : Spec (CommRingCat.of B),
        IsSimplyConnected (geometricFiber G' s') ∧ IsAlmostSimple (geometricFiber G' s')) →
      (∀ s'' : Spec (CommRingCat.of B''),
        IsSimplyConnected (geometricFiber G'' s'') ∧ IsAlmostSimple (geometricFiber G'' s'')) →
      Nonempty (G ≅ AffineWeil.groupScheme A B G') →
      Nonempty (G ≅ AffineWeil.groupScheme A B'' G'') →
      ∃ α : B'' ≃ₐ[A] B,
        Nonempty ((GroupScheme.baseChange
          (Spec.map (CommRingCat.ofHom (α : B'' →+* B)))).obj G'' ≅ G')

end Langlands.GroupScheme
