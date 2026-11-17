import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.AffineWeilRestriction

/-! # Statement: descent of a Weil-restriction presentation along one étale cover -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Descent of a Weil-restriction presentation along a single étale cover.**
Let `A → A'` be an étale ring map with `Spec A' → Spec A` surjective, and let `G` be an affine
group scheme locally of finite type over `Spec A`. Suppose the base change `G_{A'}` is isomorphic
to the Weil restriction `R_{C/A'}(H)`, where `C` is a finite, projective, étale `A'`-algebra and
`H` is a reductive group scheme over `Spec C` whose geometric fibres are almost simple. Then there
are a finite, projective, étale `A`-algebra `B` and a reductive group scheme `G'` over `Spec B`
whose geometric fibres are almost simple, such that `G ≅ R_{B/A}(G')`. -/
def AffineWeilPairSingleChartDescentStatement : Prop :=
  ∀ (A A' : Type u) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'],
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap A A'))) →
    ∀ (G : GroupScheme (Spec (CommRingCat.of A))) [IsAffine G.X.left]
      [LocallyOfFiniteType G.X.hom]
      (C : Type u) [CommRing C] [Algebra A' C] [Module.Finite A' C]
      [Module.Projective A' C] [Algebra.Etale A' C]
      (H : GroupScheme (Spec (CommRingCat.of C))) [IsAffine H.X.left]
      [LocallyOfFiniteType H.X.hom],
      IsReductive H →
      (∀ t : Spec (CommRingCat.of C), IsAlmostSimple (geometricFiber H t)) →
      Nonempty ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom (algebraMap A A')))).obj G ≅
        AffineWeil.groupScheme A' C H) →
      ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
        (_ : Module.Projective A B) (_ : Algebra.Etale A B)
        (G' : GroupScheme (Spec (CommRingCat.of B))) (_ : IsAffine G'.X.left)
        (_ : LocallyOfFiniteType G'.X.hom),
        IsReductive G' ∧
        (∀ t : Spec (CommRingCat.of B), IsAlmostSimple (geometricFiber G' t)) ∧
        Nonempty (G ≅ AffineWeil.groupScheme A B G')

end Langlands.GroupScheme
