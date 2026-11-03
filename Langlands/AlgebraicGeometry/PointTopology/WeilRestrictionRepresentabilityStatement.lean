import Langlands.AlgebraicGeometry.PointTopology.AffineWeilRestrictionRepresentability

/-! # Representability on all actual test schemes for affine Weil restriction -/

universe u

open CategoryTheory
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

/-- The canonical counit comparison represents the actual base-changed Hom
functor on every test scheme, for an affine finite-type scheme over a finite
projective coefficient algebra. -/
def WeilRestrictionRepresentabilityProperties
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Projective A B] : Prop :=
  ∀ (X : Over (Spec (CommRingCat.of B))) [IsAffine X.left]
      [LocallyOfFiniteType X.hom] (T : Over (Spec (CommRingCat.of A))),
    Function.Bijective (affineWeilRestrictionComparison A B X T)

end Langlands.AlgebraicGeometry.PointTopology
