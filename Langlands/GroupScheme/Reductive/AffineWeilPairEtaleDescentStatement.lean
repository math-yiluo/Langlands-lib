import Langlands.GroupScheme.Reductive.AlmostSimple
import Langlands.GroupScheme.AffineWeilRestriction

/-! # Statement: étale descent of Weil-restriction presentations with almost simple factors -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme

/-- **Étale-local Weil-restriction presentations with almost simple factors descend.**
Let `G` be an affine group scheme locally of finite type over `Spec A`. Let `(R i)` be a family
of étale `A`-algebras whose spectra cover `Spec A`. Suppose that for every `i` the base change
`G_{R i}` is isomorphic to the Weil restriction `R_{B' i / R i}(G₁ i)`, where `B' i` is a finite,
projective, étale `R i`-algebra with `Spec (B' i) → Spec (R i)` surjective and `G₁ i` is a
reductive group scheme over `Spec (B' i)` whose geometric fibres are almost simple. Then there
are a finite, projective, étale `A`-algebra `B` with `Spec B → Spec A` surjective and a reductive
group scheme `G'` over `Spec B` whose geometric fibres are almost simple, such that
`G ≅ R_{B/A}(G')`. Moreover the descended pair recovers every local one: for every `i` there is
an `R i`-algebra isomorphism `e : R i ⊗[A] B ≃ B' i` such that the base change of `G'` along
`Spec (B' i) → Spec B` (the spectrum of `b ↦ e (1 ⊗ b)`) is isomorphic to `G₁ i`. -/
def AffineWeilPairEtaleDescentStatement : Prop :=
  ∀ (A : Type u) [CommRing A] (G : GroupScheme (Spec (CommRingCat.of A)))
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (ι : Type u) (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra A (R i)]
    [∀ i, Algebra.Etale A (R i)]
    (B' : ι → Type u) [∀ i, CommRing (B' i)] [∀ i, Algebra (R i) (B' i)]
    [∀ i, Module.Finite (R i) (B' i)] [∀ i, Module.Projective (R i) (B' i)]
    [∀ i, Algebra.Etale (R i) (B' i)]
    (G₁ : ∀ i, GroupScheme (Spec (CommRingCat.of (B' i))))
    [∀ i, IsAffine (G₁ i).X.left] [∀ i, LocallyOfFiniteType (G₁ i).X.hom],
    (∀ s : Spec (CommRingCat.of A), ∃ i,
      s ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap A (R i))))) →
    (∀ i, Surjective (Spec.map (CommRingCat.ofHom (algebraMap (R i) (B' i))))) →
    (∀ i, IsReductive (G₁ i)) →
    (∀ i (t : Spec (CommRingCat.of (B' i))), IsAlmostSimple (geometricFiber (G₁ i) t)) →
    (∀ i, Nonempty ((GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap A (R i))))).obj G ≅
        AffineWeil.groupScheme (R i) (B' i) (G₁ i))) →
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Module.Finite A B)
      (_ : Module.Projective A B) (_ : Algebra.Etale A B)
      (G' : GroupScheme (Spec (CommRingCat.of B))) (_ : IsAffine G'.X.left)
      (_ : LocallyOfFiniteType G'.X.hom),
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap A B))) ∧
      IsReductive G' ∧
      (∀ t : Spec (CommRingCat.of B), IsAlmostSimple (geometricFiber G' t)) ∧
      Nonempty (G ≅ AffineWeil.groupScheme A B G') ∧
      ∀ i, ∃ e : R i ⊗[A] B ≃ₐ[R i] B' i,
        Nonempty ((GroupScheme.baseChange (Spec.map (CommRingCat.ofHom
          ((e : R i ⊗[A] B →+* B' i).comp
            (Algebra.TensorProduct.includeRight : B →ₐ[A] R i ⊗[A] B).toRingHom)))).obj G' ≅
          G₁ i)

end Langlands.GroupScheme
