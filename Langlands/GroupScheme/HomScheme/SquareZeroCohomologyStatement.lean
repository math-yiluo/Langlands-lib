import Langlands.GroupScheme.Cohomology.RegularCochains
import Langlands.GroupScheme.HomScheme.ConjugatorLifting
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! # Statement: low-degree cohomology controls square-zero homomorphism lifting -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.HomScheme

/-- The geometric deformation bridge: vanishing of regular degree-one and
degree-two cohomology of the reduced flat affine source gives actual relative
homomorphism lifting and lifting of every prescribed conjugator through a
square-zero affine thickening, for any smooth target group. -/
def SquareZeroHomomorphismCohomologyStatement : Prop :=
  ∀ (S : Scheme.{u}) (H G : GroupScheme S) [Smooth G.X.hom]
    (A : Type u) [CommRing A] (I : Ideal A), I ^ 2 = ⊥ →
    ∀ (a : Spec (CommRingCat.of A) ⟶ S)
      (b : Spec (CommRingCat.of (A ⧸ I)) ⟶ S)
      (w : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫ a = b),
      Flat ((baseChange a).obj H).X.hom →
      IsAffine ((baseChange a).obj H).X.left →
      Cohomology.HasVanishingLowDegreeCohomology ((baseChange b).obj H) →
      HasConjugatorLifting H G
        (Over.homMk (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) w :
          Over.mk b ⟶ Over.mk a)

end Langlands.GroupScheme.HomScheme
