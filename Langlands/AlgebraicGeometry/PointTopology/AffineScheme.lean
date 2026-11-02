import Langlands.AlgebraicGeometry.PointTopology.Affine
import Langlands.AlgebraicGeometry.PointTopology.ProductRingPoints
import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Evaluation topology on points of arbitrary affine schemes

The point carrier is the existing actual morphism set in `Over (Spec R)`.
The canonical isomorphism with the spectrum of global sections gives its
evaluation topology.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- The actual global-section ring, named to record the structure morphism. -/
def AffineCoordinateRing (X : Over (Spec (CommRingCat.of R))) :=
  Γ(X.left, ⊤)

instance (X : Over (Spec (CommRingCat.of R))) :
    CommRing (AffineCoordinateRing R X) :=
  inferInstanceAs (CommRing Γ(X.left, ⊤))

/-- The structure ring map expressed through the canonical affine isomorphism. -/
def affineCoordinateMap (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    R →+* AffineCoordinateRing R X :=
  (Spec.preimage (X.left.isoSpec.inv ≫ X.hom)).hom

instance (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    Algebra R (AffineCoordinateRing R X) :=
  (affineCoordinateMap R X).toAlgebra

theorem affineCoordinateSpecMap (X : Over (Spec (CommRingCat.of R)))
    [IsAffine X.left] :
    Spec.algebraMap R (AffineCoordinateRing R X) = X.left.isoSpec.inv ≫ X.hom :=
  Spec.map_preimage _

/-- The canonical affine isomorphism respects the specified base morphism. -/
def affineSchemeOverIso (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    X ≅ ringTest R (AffineCoordinateRing R X) :=
  Over.isoMk X.left.isoSpec (by
    change X.left.isoSpec.hom ≫ Spec.algebraMap R (AffineCoordinateRing R X) = X.hom
    rw [affineCoordinateSpecMap, Iso.hom_inv_id_assoc])

/-- Actual relative points of an affine scheme are its global-section algebra maps. -/
def affineSchemePointEquiv (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (S : Type u) [CommRing S] [Algebra R S] :
    RingPoint R X S ≃ AlgPoint R (AffineCoordinateRing R X) S :=
  (Iso.homCongr (Iso.refl (ringTest R S)) (affineSchemeOverIso R X)).trans
    ((affineRingPointEquiv R (AffineCoordinateRing R X) S).trans AlgPoint.algHomEquiv.symm)

instance (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (S : Type u) [CommRing S] [Algebra R S] [TopologicalSpace S] :
    TopologicalSpace (RingPoint R X S) :=
  TopologicalSpace.induced (affineSchemePointEquiv R X S) inferInstance

/-- The topology on actual affine scheme points is the global-section evaluation topology. -/
def affineSchemePointHomeomorph (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    (S : Type u) [CommRing S] [Algebra R S] [TopologicalSpace S] :
    RingPoint R X S ≃ₜ AlgPoint R (AffineCoordinateRing R X) S :=
  (affineSchemePointEquiv R X S).toHomeomorphOfIsInducing ⟨rfl⟩

end Langlands.AlgebraicGeometry.PointTopology
