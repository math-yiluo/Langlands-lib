import Langlands.GroupScheme.AffineWeilRestriction
import Langlands.TauCeti.RingTheory.WeilRestriction.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smoothness of the actual affine group-scheme Weil restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- Smoothness of the actual global-section algebra is exactly smoothness of
an affine scheme's structure morphism. -/
theorem affineCoordinate_smooth_iff
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    Algebra.Smooth R (AffineCoordinateRing R X) ↔ Smooth X.hom := by
  rw [← RingHom.smooth_algebraMap]
  change (CommRingCat.ofHom
    (algebraMap R (AffineCoordinateRing R X))).hom.Smooth ↔ _
  rw [← HasRingHomProperty.Spec_iff (P := @Smooth) (Q := @RingHom.Smooth)
    (φ := CommRingCat.ofHom (algebraMap R (AffineCoordinateRing R X)))]
  change Smooth (Spec.algebraMap R (AffineCoordinateRing R X)) ↔ _
  rw [affineCoordinateSpecMap]
  change Smooth (X.left.isoSpec.inv ≫ X.hom) ↔ Smooth X.hom
  constructor
  · intro h
    have := h
    have h' : Smooth (X.left.isoSpec.hom ≫ (X.left.isoSpec.inv ≫ X.hom)) := inferInstance
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h'
  · intro h
    have := h
    infer_instance

instance affineCoordinate_smooth
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] [Smooth X.hom] :
    Algebra.Smooth R (AffineCoordinateRing R X) :=
  (affineCoordinate_smooth_iff R X).mpr inferInstance

end Langlands.AlgebraicGeometry.PointTopology

namespace Langlands.GroupScheme.AffineWeil

open Langlands.Algebra Langlands.AlgebraicGeometry.PointTopology

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
  [Module.Finite A B] [Module.Projective A B]
  (G : GroupScheme (Spec (CommRingCat.of B)))
  [IsAffine G.X.left] [Smooth G.X.hom]

/-- The actual finite-type restriction coordinates agree with the finite-presentation
restriction coordinates; smoothness supplies the finite-presentation hypothesis. -/
def finitePresentationCoordinateEquiv :
    WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X) ≃ₐ[A]
      TauCeti.Algebra.WeilRestriction A B (AffineCoordinateRing B G.X) :=
  WeilRestrictionFiniteType.finitePresentationAlgEquiv A B (AffineCoordinateRing B G.X)

/-- The comparison preserves the actual universal tensor-valued point. -/
theorem finitePresentationCoordinateEquiv_universalPoint :
    (Algebra.TensorProduct.lTensor B
      (finitePresentationCoordinateEquiv A B G).toAlgHom).comp
        (WeilRestrictionFiniteType.universalPoint A B (AffineCoordinateRing B G.X)) =
      TauCeti.Algebra.WeilRestriction.universalPoint A B (AffineCoordinateRing B G.X) :=
  WeilRestrictionFiniteType.finitePresentationAlgEquiv_universalPoint A B
    (AffineCoordinateRing B G.X)

/-- The actual coordinate algebra of the affine restriction is smooth over the ground ring. -/
theorem coordinateAlgebra_smooth :
    Algebra.Smooth A (WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X)) :=
  Algebra.Smooth.of_equiv (finitePresentationCoordinateEquiv A B G).symm

/-- Restriction along a finite projective algebra preserves smoothness of the actual
smooth affine group scheme. -/
theorem smooth_groupScheme : Smooth (groupScheme A B G).X.hom := by
  have := coordinateAlgebra_smooth A B G
  change Smooth (Spec.map (CommRingCat.ofHom
    (algebraMap A (WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X)))))
  rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
  change (algebraMap A (WeilRestrictionFiniteType A B (AffineCoordinateRing B G.X))).Smooth
  rw [RingHom.smooth_algebraMap]
  infer_instance

end Langlands.GroupScheme.AffineWeil
