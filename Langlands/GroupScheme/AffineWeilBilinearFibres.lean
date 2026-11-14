import Langlands.GroupScheme.AffineWeilBilinearSpecialFibre

/-! # Geometrically connected fibres of actual restricted bilinear groups -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.AffineWeilBilinear

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  {I : Type u} [Fintype I] (c : I → I → B)

attribute [local instance] bilinear_isAffine bilinear_locallyOfFiniteType
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The actual restriction of a bilinear coordinate group has geometrically
connected fibres, without assuming that the coefficient algebra is free. -/
theorem restriction_geometricallyConnected :
    GeometricallyConnected (AffineWeil.groupScheme A B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X.hom := by
  constructor
  apply (geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun T : Scheme.{u} => ConnectedSpace T) (R := A)
    (f := (AffineWeil.groupScheme A B
      (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X.hom)).mpr
  intro k _ _
  change ConnectedSpace (AffineWeil.BaseChange.source A B k
    (BilinearCoordinate.groupScheme (CommRingCat.of B) c)).X.left
  have h := properties k (k ⊗[A] B)
    (BilinearCoordinate.mappedCoefficients (fibreCoefficientMap A B k) c)
    (Module.finBasis k (k ⊗[A] B))
  exact (smooth_connected_of_groupIso (restrictionFibreIso A B k c) h.1 h.2.1).2

end Langlands.GroupScheme.AffineWeilBilinear
