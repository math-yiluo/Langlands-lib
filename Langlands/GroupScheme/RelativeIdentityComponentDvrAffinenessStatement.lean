import Langlands.GroupScheme.RelativeIdentityComponent
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Affineness of the relative identity component over a DVR

This is the affineness target for any actual open subgroup representing the
all-test relative identity-component criterion of a smooth affine group scheme.
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeIdentityComponent

/-- Over every discrete valuation ring, a represented relative identity component
of a smooth affine group scheme is affine over the base. -/
def SmoothDvrAffinenessStatement : Prop :=
  ∀ (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (G : GroupScheme (Spec (CommRingCat.of R))),
    Smooth G.X.hom → IsAffineHom G.X.hom →
      ∀ (H : GroupScheme (Spec (CommRingCat.of R))) (i : H ⟶ G),
        IsRelativeIdentityComponent G i → IsAffineHom H.X.hom

end Langlands.GroupScheme.RelativeIdentityComponent
