import Langlands.AlgebraicGeometry.Picard.RelativePicardZero
import Mathlib.RingTheory.Artinian.Ring
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

/-! # Lifting Picard-zero families along elementary Artinian thickenings -/

universe u

open CategoryTheory AlgebraicGeometry IsLocalRing

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard

/-- Formal smoothness of the rigidified Picard-zero functor of an abelian scheme along
elementary thickenings of local Artinian rings. Let `φ : B' → B` be a surjection of local
Artinian rings whose kernel is killed by the maximal ideal of `B'`, and let
`β : Spec B' ⟶ S`. Every geometric Picard-zero rigidified family on `A` over `Spec B`, viewed
over `S` through `Spec φ ≫ β`, is the actual rigidified pullback along `Spec φ` of a geometric
Picard-zero rigidified family over `Spec B'`. -/
def PicardZeroArtinianLiftingStatement : Prop :=
  ∀ (S : Scheme.{u}) (A : AbelianScheme S) (B' B : Type u) [CommRing B'] [CommRing B]
    [IsLocalRing B'] [IsLocalRing B] [IsArtinianRing B'] [IsArtinianRing B]
    (φ : B' →+* B), Function.Surjective φ → maximalIdeal B' * RingHom.ker φ = ⊥ →
      ∀ (β : Spec (CommRingCat.of B') ⟶ S)
        (M : RigidifiedFamily A (Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β))),
        IsPicardZeroFamily A M →
          ∃ M' : RigidifiedFamily A (Over.mk β), IsPicardZeroFamily A M' ∧
            Nonempty ((RigidifiedLineBundle.relativePullback A.X.hom (unitSection A)
              (unitSection_comp A)
              (Over.homMk (Spec.map (CommRingCat.ofHom φ)) rfl :
                Over.mk (Spec.map (CommRingCat.ofHom φ) ≫ β) ⟶ Over.mk β)).obj M' ≅ M)

end Langlands.AbelianScheme
