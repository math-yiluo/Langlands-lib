import Langlands.AlgebraicGeometry.PointTopology.AffineProductRingTopologyStatement
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Proof that affine point topology commutes with products of value rings

Construct the algebra-map product homeomorphism and identify its transport with
the actual relative scheme-point restriction map.
-/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C : Type u) [CommRing C]

private theorem affineRingPointEquiv_changeRing
    (A S T : Type u) [CommRing A] [CommRing S] [CommRing T]
    [Algebra C A] [Algebra C S] [Algebra C T]
    (f : S →ₐ[C] T) (p : RingPoint C (ringTest C A) S) :
    affineRingPointEquiv C A T (p.changeRing f) =
      f.comp (affineRingPointEquiv C A S p) := by
  apply AlgHom.coe_ringHom_injective
  let p₀ : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of A) := p.left
  change (Spec.preimage (Spec.map (CommRingCat.ofHom f.toRingHom) ≫ p₀)).hom =
    f.toRingHom.comp (Spec.preimage p₀).hom
  rw [Spec.preimage_comp, Spec.preimage_map, CommRingCat.hom_comp]
  rfl

/-- The affine coordinate equivalence respects change of coefficient algebra. -/
theorem affineSchemePointEquiv_changeRing
    (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left]
    (S T : Type u) [CommRing S] [CommRing T] [Algebra C S] [Algebra C T]
    (f : S →ₐ[C] T) (p : RingPoint C X S) :
    affineSchemePointEquiv C X T (p.changeRing f) =
      AlgPoint.mapCoefficients f (affineSchemePointEquiv C X S p) := by
  let p₀ : ringTest C S ⟶ X := p
  change affineRingPointEquiv C (AffineCoordinateRing C X) T
      (𝟙 (ringTest C T) ≫ (ringTestMap C f ≫ p₀) ≫ (affineSchemeOverIso C X).hom) =
    f.comp (affineRingPointEquiv C (AffineCoordinateRing C X) S
      (𝟙 (ringTest C S) ≫ p₀ ≫ (affineSchemeOverIso C X).hom))
  simp only [Category.id_comp, Category.assoc]
  exact affineRingPointEquiv_changeRing C (AffineCoordinateRing C X) S T f
    (p₀ ≫ (affineSchemeOverIso C X).hom)

private def algPointProductValueHomeomorph
    (A : Type u) [CommRing A] [Algebra C A]
    {ι : Type u} (R : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
    [∀ i, TopologicalSpace (R i)] :
    AlgPoint C A (∀ i, R i) ≃ₜ ∀ i, AlgPoint C A (R i) where
  toFun p i := AlgPoint.mapCoefficients (Pi.evalAlgHom C R i) p
  invFun p := AlgPoint.ofAlgHom (AlgHom.pi (fun i => (p i).toAlgHom))
  left_inv p := by
    apply AlgPoint.ext
    intro a
    funext i
    rfl
  right_inv p := by
    funext i
    apply AlgPoint.ext
    intro a
    rfl
  continuous_toFun := continuous_pi (fun i =>
    AlgPoint.continuous_mapCoefficients _ (continuous_apply i))
  continuous_invFun := (AlgPoint.continuous_iff _).mpr (fun a =>
    continuous_pi (fun i => (AlgPoint.continuous_eval a).comp (continuous_apply i)))

theorem productPointMap_isHomeomorph
    {ι : Type u} (R : ι → Type u)
    [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)]
    [∀ i, TopologicalSpace (R i)]
    (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left] :
    IsHomeomorph (productPointMap C R X) := by
  let e : RingPoint C X (∀ i, R i) ≃ₜ ∀ i, RingPoint C X (R i) :=
    (affineSchemePointHomeomorph C X (∀ i, R i)).trans
      ((algPointProductValueHomeomorph C (AffineCoordinateRing C X) R).trans
        (Homeomorph.piCongrRight (fun i =>
          (affineSchemePointHomeomorph C X (R i)).symm)))
  have he : (e : RingPoint C X (∀ i, R i) → ∀ i, RingPoint C X (R i)) =
      productPointMap C R X := by
    funext p i
    apply (affineSchemePointEquiv C X (R i)).injective
    change affineSchemePointEquiv C X (R i)
        ((affineSchemePointEquiv C X (R i)).symm
          (AlgPoint.mapCoefficients (Pi.evalAlgHom C R i)
            (affineSchemePointEquiv C X (∀ i, R i) p))) =
      affineSchemePointEquiv C X (R i) (p.changeRing (Pi.evalAlgHom C R i))
    rw [Equiv.apply_symm_apply, affineSchemePointEquiv_changeRing]
  rw [← he]
  exact e.isHomeomorph

/-- The exact affine product-value-ring topology target. -/
theorem affineProductRingTopology : AffineProductRingTopologyStatement.{u} := by
  intro C _ ι R _ _ _ X _
  exact productPointMap_isHomeomorph C R X

end Langlands.AlgebraicGeometry.PointTopology
