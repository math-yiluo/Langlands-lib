import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMaps
import Langlands.AlgebraicGeometry.PointTopology.AffineTopologyFamily
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType

/-!
# Topology families on actual finite-type affine scheme points
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R : Type u) [CommRing R]

/-- Finite type of the actual global-section algebra is exactly local finite
 type of the structure morphism. Affineness supplies quasi-compactness. -/
theorem affineCoordinate_finiteType_iff
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] :
    Algebra.FiniteType R (AffineCoordinateRing R X) ↔ LocallyOfFiniteType X.hom := by
  rw [← RingHom.finiteType_algebraMap]
  change (CommRingCat.ofHom
    (algebraMap R (AffineCoordinateRing R X))).hom.FiniteType ↔ _
  rw [← HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (Q := @RingHom.FiniteType)
    (φ := CommRingCat.ofHom (algebraMap R (AffineCoordinateRing R X)))]
  change LocallyOfFiniteType (Spec.algebraMap R (AffineCoordinateRing R X)) ↔ _
  rw [affineCoordinateSpecMap]
  change LocallyOfFiniteType (X.left.isoSpec.inv ≫ X.hom) ↔ LocallyOfFiniteType X.hom
  constructor
  · intro h
    have := h
    have h' : LocallyOfFiniteType
        (X.left.isoSpec.hom ≫ (X.left.isoSpec.inv ≫ X.hom)) := inferInstance
    simpa only [← Category.assoc, Iso.hom_inv_id, Category.id_comp] using h'
  · intro h
    have := h
    infer_instance

instance affineCoordinate_finiteType
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]
    [LocallyOfFiniteType X.hom] : Algebra.FiniteType R (AffineCoordinateRing R X) :=
  (affineCoordinate_finiteType_iff R X).mpr inferInstance

/-- This is why local finite type is full finite type for this affine family. -/
theorem affineStructure_quasiCompact
    (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left] : QuasiCompact X.hom :=
  inferInstance

/-- The finite-type condition on a spectrum retains its specified base algebra. -/
theorem ringTest_locallyOfFiniteType_iff
    (A : Type u) [CommRing A] [Algebra R A] :
    LocallyOfFiniteType (ringTest R A).hom ↔ Algebra.FiniteType R A := by
  change LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap R A))) ↔ _
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType) (Q := @RingHom.FiniteType)]
  change (algebraMap R A).FiniteType ↔ _
  exact RingHom.finiteType_algebraMap

instance ringTest_locallyOfFiniteType
    (A : Type u) [CommRing A] [Algebra R A] [Algebra.FiniteType R A] :
    LocallyOfFiniteType (ringTest R A).hom :=
  (ringTest_locallyOfFiniteType_iff R A).mpr inferInstance

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The actual spectrum relative points are the actual algebra maps. -/
def spectrumAlgebraPointEquiv (A : Type u) [CommRing A] [Algebra R A] :
    RingPoint R (ringTest R A) S ≃ AlgPoint R A S :=
  (affineRingPointEquiv R A S).trans AlgPoint.algHomEquiv.symm

/-- The direct algebra-map comparison agrees with the global-section topology. -/
def spectrumAlgebraPointHomeomorph [TopologicalSpace S]
    (A : Type u) [CommRing A] [Algebra R A] :
    RingPoint R (ringTest R A) S ≃ₜ AlgPoint R A S := by
  let e := (affineSchemePointHomeomorph R (ringTest R A) S).trans
    (AlgPoint.congr (spectrumCoordinateAlgEquiv R A))
  have he : (e : RingPoint R (ringTest R A) S → AlgPoint R A S) =
      spectrumAlgebraPointEquiv R S A := by
    funext p
    change AlgPoint.precomp (spectrumCoordinateAlgEquiv R A).symm.toAlgHom
      (affineSchemePointEquiv R (ringTest R A) S p) = _
    rw [affineSchemePointEquiv_spectrum]
    ext a
    change (affineRingPointEquiv R A S p)
      (spectrumCoordinateAlgEquiv R A
        ((spectrumCoordinateAlgEquiv R A).symm a)) =
      (affineRingPointEquiv R A S p) a
    rw [AlgEquiv.apply_symm_apply]
  exact (spectrumAlgebraPointEquiv R S A).toHomeomorphOfIsInducing (he ▸ e.isInducing)

@[simp] theorem spectrumAlgebraPointHomeomorph_apply [TopologicalSpace S]
    (A : Type u) [CommRing A] [Algebra R A]
    (p : RingPoint R (ringTest R A) S) :
    spectrumAlgebraPointHomeomorph R S A p = spectrumAlgebraPointEquiv R S A p := rfl

/-- Arbitrary topology assignments on actual points of all finite-type affine
 schemes over the specified base. No functorial or comparison axiom is assumed. -/
def AffineSchemeTopologyFamily :=
  (X : Over (Spec (CommRingCat.of R))) → [IsAffine X.left] →
    [LocallyOfFiniteType X.hom] → TopologicalSpace (RingPoint R X S)

/-- The independently constructed global-section evaluation topology family. -/
def evaluationAffineSchemeTopologyFamily [TopologicalSpace S] :
    AffineSchemeTopologyFamily R S := fun _ _ _ => inferInstance

/-- Transport an algebra-point assignment along the actual global-section
 point equivalence, using the proved finite-type bridge. -/
def algebraTopologyFamilyToSchemes (T : AffinePointTopologyFamily R S) :
    AffineSchemeTopologyFamily R S :=
  fun X _ _ => TopologicalSpace.induced (affineSchemePointEquiv R X S)
    (T (CommAlgCat.of R (AffineCoordinateRing R X)))

/-- Restrict a scheme-point assignment to actual spectra and transport by the
 direct algebra-map point equivalence. -/
def schemeTopologyFamilyToAlgebras (T : AffineSchemeTopologyFamily R S) :
    AffinePointTopologyFamily R S :=
  fun A _ => TopologicalSpace.induced (spectrumAlgebraPointEquiv R S A).symm
    (T (ringTest R A))

end Langlands.AlgebraicGeometry.PointTopology
