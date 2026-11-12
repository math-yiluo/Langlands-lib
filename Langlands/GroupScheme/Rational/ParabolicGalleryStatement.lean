import Langlands.GroupScheme.Rational.ParabolicGallery

/-! # Existence targets for rational parabolic galleries -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Any two actual rational parabolics with the same embedded rational Levi
are joined by a finite chain of actual rank-one walls. -/
def RationalParabolicGalleryStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (L : GroupScheme (Spec (CommRingCat.of k))) (j : L ⟶ G)
      (F F' : SubgroupFunctor G),
      IsRationalParabolicWithLevi j F → IsRationalParabolicWithLevi j F' →
        HasRationalParabolicGallery j F F'

/-- If two rational parabolics with the same embedded Levi agree inside the
centralizer of a specified central split subtorus of that Levi, they can be
joined using only rank-one walls nonzero on that torus. -/
def RationalParabolicGalleryAvoidingStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (L : GroupScheme (Spec (CommRingCat.of k)))
      (B : CommGroupScheme (Spec (CommRingCat.of k)))
      (j : L ⟶ G) (b : B.toGrp ⟶ L),
      IsSplitSubtorus b → IsCentral b →
      ∀ F F' : SubgroupFunctor G,
        IsRationalParabolicWithLevi j F → IsRationalParabolicWithLevi j F' →
        F ⊓ torusCentralizer (b ≫ j) = F' ⊓ torusCentralizer (b ≫ j) →
          HasRationalParabolicGalleryAvoiding b j F F'

/-- The ordinary and central-torus-restricted rational gallery targets. -/
def RationalParabolicGalleryStatements : Prop :=
  RationalParabolicGalleryStatement.{u} ∧ RationalParabolicGalleryAvoidingStatement.{u}

end Langlands.GroupScheme
