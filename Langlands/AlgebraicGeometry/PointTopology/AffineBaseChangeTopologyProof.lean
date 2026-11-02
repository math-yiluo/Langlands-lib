import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyStatement

/-!
# Topology of actual affine base change

The tensor-coordinate presentation identifies the original pullback-adjunction
map with the scalar-extension homeomorphism.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

variable (C D A : Type u)
variable [CommRing C] [CommRing D] [CommRing A]
variable [Algebra C D] [Algebra C A] [Algebra D A] [IsScalarTower C D A]
variable (X : Over (Spec (CommRingCat.of C))) [IsAffine X.left]

/-- Restriction to the original coordinates is the first pullback projection. -/
theorem ringBaseChangeAffineOverIso_hom_fst :
    (ringBaseChangeAffineOverIso C D X).hom.left ≫
      Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight :
          AffineCoordinateRing C X →ₐ[C]
            D ⊗[C] AffineCoordinateRing C X).toRingHom) =
      pullback.fst X.hom (Spec.algebraMap C D) ≫ X.left.isoSpec.hom := by
  let F :=
    ((Over.pullback (Spec.algebraMap C D)).map (affineSchemeOverIso C X).hom).left
  let S := (pullbackSymmetry
    (Spec.algebraMap C (AffineCoordinateRing C X)) (Spec.algebraMap C D)).hom
  let T := (pullbackSpecIso C D (AffineCoordinateRing C X)).hom
  let R := Spec.map (CommRingCat.ofHom
    (Algebra.TensorProduct.includeRight :
      AffineCoordinateRing C X →ₐ[C] D ⊗[C] AffineCoordinateRing C X).toRingHom)
  have h₁ : T ≫ R =
      pullback.snd (Spec.algebraMap C D)
        (Spec.algebraMap C (AffineCoordinateRing C X)) :=
    pullbackSpecIso_hom_snd C D (AffineCoordinateRing C X)
  have h₂ : S ≫ pullback.snd (Spec.algebraMap C D)
      (Spec.algebraMap C (AffineCoordinateRing C X)) =
        pullback.fst (Spec.algebraMap C (AffineCoordinateRing C X))
          (Spec.algebraMap C D) :=
    pullbackSymmetry_hom_comp_snd _ _
  have h₃ : F ≫
      pullback.fst (Spec.algebraMap C (AffineCoordinateRing C X))
        (Spec.algebraMap C D) =
      pullback.fst X.hom (Spec.algebraMap C D) ≫ X.left.isoSpec.hom :=
    pullback.lift_fst _ _ _
  change (F ≫ (S ≫ T)) ≫ R = _
  exact ((Category.assoc F (S ≫ T) R).trans
    (congrArg (fun k => F ≫ k) (Category.assoc S T R))).trans
      ((congrArg (fun k => F ≫ (S ≫ k)) h₁).trans
        ((congrArg (fun k => F ≫ k) h₂).trans h₃))

variable [TopologicalSpace A]

/-- The inverse point comparison restricts a tensor point to `1 ⊗ b`. -/
theorem affineBaseChange_inverse_coordinates
    (q : RingPoint D (ringBaseChange C D X) A) :
    affineSchemePointEquiv C X A ((ringPointBaseChangeEquiv C D A X).symm q) =
      (AlgPoint.baseChangeEquiv C D (AffineCoordinateRing C X) A).symm
        (specPointEquiv D (D ⊗[C] AffineCoordinateRing C X) A
          (affinePresentationPointHomeomorph D A
            (D ⊗[C] AffineCoordinateRing C X)
            (ringBaseChangeAffineOverIso C D X) q)) := by
  let e := ringBaseChangeAffineOverIso C D X
  let t : AlgPoint D (D ⊗[C] AffineCoordinateRing C X) A :=
    specPointEquiv D (D ⊗[C] AffineCoordinateRing C X) A
      (affinePresentationPointHomeomorph D A
        (D ⊗[C] AffineCoordinateRing C X) e q)
  let i : CommRingCat.of (AffineCoordinateRing C X) ⟶
      CommRingCat.of (D ⊗[C] AffineCoordinateRing C X) :=
    CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight :
        AffineCoordinateRing C X →ₐ[C]
          D ⊗[C] AffineCoordinateRing C X).toRingHom
  have ht : Spec.map (CommRingCat.ofHom t.toAlgHom.toRingHom) =
      q.left ≫ e.hom.left :=
    (Spec.map_preimage _).trans
      (affinePresentationPointHomeomorph_apply D A
        (D ⊗[C] AffineCoordinateRing C X) e q)
  have h :
      CommRingCat.ofHom
        (affineSchemePointEquiv C X A
          ((ringPointBaseChangeEquiv C D A X).symm q)).toAlgHom.toRingHom =
      i ≫ CommRingCat.ofHom t.toAlgHom.toRingHom := by
    apply Spec.map_injective
    exact (affineSchemePointEquiv_spec C A _).trans
      ((congrArg (fun k => k ≫ X.left.isoSpec.hom)
        (ringPointBaseChangeEquiv_symm_left C D A X q)).trans
        ((Category.assoc q.left _ _).trans
          ((congrArg (fun k => q.left ≫ k)
            (ringBaseChangeAffineOverIso_hom_fst C D X).symm).trans
            ((Category.assoc q.left e.hom.left (Spec.map i)).symm.trans
              ((congrArg (fun k => k ≫ Spec.map i) ht.symm).trans
                (Spec.map_comp i (CommRingCat.ofHom t.toAlgHom.toRingHom)).symm)))))
  apply AlgPoint.ext
  intro b
  exact congrArg
    (fun f : CommRingCat.of (AffineCoordinateRing C X) ⟶ CommRingCat.of A => f.hom b) h

theorem isHomeomorph_ringPointBaseChangeEquiv [IsTopologicalRing A] :
    IsHomeomorph (ringPointBaseChangeEquiv C D A X) := by
  let e : RingPoint D (ringBaseChange C D X) A ≃ₜ RingPoint C X A :=
    (((affinePresentationPointHomeomorph D A
      (D ⊗[C] AffineCoordinateRing C X)
      (ringBaseChangeAffineOverIso C D X)).trans
        (specPointHomeomorph D (D ⊗[C] AffineCoordinateRing C X) A)).trans
      (AlgPoint.baseChangeHomeomorph C D (AffineCoordinateRing C X) A).symm).trans
        (affineSchemePointHomeomorph C X A).symm
  have he (q : RingPoint D (ringBaseChange C D X) A) :
      e q = (ringPointBaseChangeEquiv C D A X).symm q := by
    apply (affineSchemePointEquiv C X A).injective
    change (affineSchemePointEquiv C X A)
      ((affineSchemePointEquiv C X A).symm _) = _
    exact ((affineSchemePointEquiv C X A).apply_symm_apply _).trans
      (affineBaseChange_inverse_coordinates C D A X q).symm
  have hf : (e.symm : RingPoint C X A → RingPoint D (ringBaseChange C D X) A) =
      ringPointBaseChangeEquiv C D A X := by
    funext p
    apply (ringPointBaseChangeEquiv C D A X).symm.injective
    exact (he (e.symm p)).symm.trans
      ((e.apply_symm_apply p).trans
        ((ringPointBaseChangeEquiv C D A X).symm_apply_apply p).symm)
  exact hf ▸ e.symm.isHomeomorph

/-- The exact evaluation-topology comparison for actual affine base change. -/
theorem affineBaseChangeTopology : AffineBaseChangeTopologyStatement.{u} := by
  intro C D A _ _ _ _ _ _ _ _ _ X _
  exact isHomeomorph_ringPointBaseChangeEquiv C D A X

end Langlands.AlgebraicGeometry.PointTopology
