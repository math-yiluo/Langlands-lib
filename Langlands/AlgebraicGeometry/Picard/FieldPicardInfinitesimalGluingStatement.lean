import Langlands.AlgebraicGeometry.Picard.InfinitesimalGluing
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-! # Infinitesimal gluing for actual field Picard groupoids: statement -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Actual line bundles and their actual isomorphisms glue across affine
ring pullback squares with one surjective map having nilpotent kernel. -/
def FieldPicardInfinitesimalGluingStatement : Prop :=
  ∀ (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)), IsProper f →
    ∀ (R A B C : Type u) [CommRing R] [CommRing A] [CommRing B] [CommRing C]
      [Algebra k R] [Algebra k A] [Algebra k B] [Algebra k C]
      (p : R →ₐ[k] A) (q : R →ₐ[k] B) (a : A →ₐ[k] C) (b : B →ₐ[k] C)
      (h : IsPullback (CommRingCat.ofHom p.toRingHom) (CommRingCat.ofHom q.toRingHom)
        (CommRingCat.ofHom a.toRingHom) (CommRingCat.ofHom b.toRingHom)),
      Function.Surjective b → IsNilpotent (RingHom.ker b.toRingHom) →
        (PicardGroupoid.affineSquareComparison f p q a b h).IsEquivalence

end Langlands.AlgebraicGeometry.Picard
