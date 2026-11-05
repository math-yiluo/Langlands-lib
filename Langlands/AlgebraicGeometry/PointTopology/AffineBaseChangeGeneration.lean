import Langlands.AlgebraicGeometry.PointTopology.AffineBaseChangeTopologyProof

/-! # Generation of the actual affine base-change coordinate algebra -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R D : Type u) [CommRing R] [CommRing D] [Algebra R D]
  (X : Over (Spec (CommRingCat.of R))) [IsAffine X.left]

/-- The actual pullback's global sections are its canonical tensor algebra. -/
def ringBaseChangeCoordinateAlgEquiv :
    (D ⊗[R] AffineCoordinateRing R X) ≃ₐ[D]
      AffineCoordinateRing D (ringBaseChange R D X) :=
  (spectrumCoordinateAlgEquiv D (D ⊗[R] AffineCoordinateRing R X)).symm.trans
    (affineCoordinateAlgEquiv D (ringBaseChangeAffineOverIso R D X))

set_option backward.isDefEq.respectTransparency false in
private theorem coordinateEquiv_spec :
    Spec.map (CommRingCat.ofHom
      (ringBaseChangeCoordinateAlgEquiv R D X).toRingHom) =
      (ringBaseChange R D X).left.isoSpec.inv ≫
        (ringBaseChangeAffineOverIso R D X).hom.left := by
  change Spec.map
      ((Scheme.ΓSpecIso
          (CommRingCat.of (D ⊗[R] AffineCoordinateRing R X))).inv ≫
        (ringBaseChangeAffineOverIso R D X).hom.left.appTop) = _
  rw [Spec.map_comp, ← Scheme.isoSpec_Spec_inv]
  exact Scheme.isoSpec_inv_naturality _

set_option backward.isDefEq.respectTransparency false in
/-- The right tensor inclusion is exactly pullback along the first projection. -/
theorem ringBaseChangeCoordinateAlgEquiv_one_tmul (a : AffineCoordinateRing R X) :
    ringBaseChangeCoordinateAlgEquiv R D X (1 ⊗ₜ[R] a) =
      (pullback.fst X.hom (Spec.algebraMap R D)).appTop.hom a := by
  have h :
      CommRingCat.ofHom
        ((ringBaseChangeCoordinateAlgEquiv R D X).toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            AffineCoordinateRing R X →ₐ[R] D ⊗[R] AffineCoordinateRing R X).toRingHom) =
        (pullback.fst X.hom (Spec.algebraMap R D)).appTop := by
    apply Spec.map_injective
    rw [show CommRingCat.ofHom
        ((ringBaseChangeCoordinateAlgEquiv R D X).toRingHom.comp
          (Algebra.TensorProduct.includeRight :
            AffineCoordinateRing R X →ₐ[R] D ⊗[R] AffineCoordinateRing R X).toRingHom) =
        CommRingCat.ofHom
          (Algebra.TensorProduct.includeRight :
            AffineCoordinateRing R X →ₐ[R] D ⊗[R] AffineCoordinateRing R X).toRingHom ≫
        CommRingCat.ofHom
          (ringBaseChangeCoordinateAlgEquiv R D X).toRingHom from rfl]
    rw [Spec.map_comp, coordinateEquiv_spec, Category.assoc,
      ringBaseChangeAffineOverIso_hom_fst]
    exact (Iso.inv_comp_eq (ringBaseChange R D X).left.isoSpec).mpr
      (Scheme.isoSpec_hom_naturality _).symm
  exact congrArg (fun f => f.hom a) h

/-- The original global sections generate all generic coordinates after adjoining
the new base scalars. -/
theorem adjoin_range_baseChange_fst_eq_top :
    Algebra.adjoin (A := AffineCoordinateRing D (ringBaseChange R D X)) D
      (Set.range ((pullback.fst X.hom (Spec.algebraMap R D)).appTop.hom :
        AffineCoordinateRing R X →+* AffineCoordinateRing D (ringBaseChange R D X))) =
      ⊤ := by
  have ht := Algebra.TensorProduct.adjoin_one_tmul_image_eq_top
    (R := R) (A := D) (B := AffineCoordinateRing R X)
    Set.univ (Algebra.adjoin_univ R _)
  have hm := congrArg
    (fun A : Subalgebra D (D ⊗[R] AffineCoordinateRing R X) =>
      A.map (ringBaseChangeCoordinateAlgEquiv R D X).toAlgHom) ht
  rw [AlgHom.map_adjoin, Algebra.map_top,
    (AlgHom.range_eq_top _).mpr (ringBaseChangeCoordinateAlgEquiv R D X).surjective] at hm
  convert hm using 1
  congr 1
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨1 ⊗ₜ[R] b, ⟨b, Set.mem_univ _, rfl⟩,
      ringBaseChangeCoordinateAlgEquiv_one_tmul R D X b⟩
  · rintro ⟨t, ⟨b, _, rfl⟩, rfl⟩
    exact ⟨b, (ringBaseChangeCoordinateAlgEquiv_one_tmul R D X b).symm⟩

end Langlands.AlgebraicGeometry.PointTopology
