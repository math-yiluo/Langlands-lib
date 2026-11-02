import Langlands.AlgebraicGeometry.ProjectiveTensorClosedLocus
import Langlands.Algebra.ProjectiveTensorQuotient
import Mathlib.AlgebraicGeometry.Pullbacks

/-! # Affine product factorization through tensor equations -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry

open Langlands.Algebra.ProjectiveTensorCoefficients

/-- An affine morphism factors through an ideal quotient precisely when its
ring map kills the ideal. -/
theorem affine_factorsThrough_quotient_iff {A B : Type u}
    [CommRing A] [CommRing B] (J : Ideal A) (f : A →+* B) :
    (∃ z : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of (A ⧸ J)),
      z ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) =
        Spec.map (CommRingCat.ofHom f)) ↔ J ≤ RingHom.ker f := by
  rw [factorsThrough_affineQuotient_iff (A := CommRingCat.of A),
    ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.hom_comp]
  change J ≤ RingHom.ker
    ((Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm.toRingHom.comp f) ↔ _
  erw [RingHom.ker_comp_of_injective f
    (Scheme.ΓSpecIso (CommRingCat.of B)).commRingCatIsoToRingEquiv.symm.injective]

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  [Algebra R A] [Algebra R B] [Algebra R C]

/-- The coefficient locus is equivalent on affine tests to factoring the
whole tensor spectrum through the closed tensor-ideal quotient. -/
theorem affine_coefficientLocus_iff_tensorQuotient [Module.Projective R C]
    (I : Ideal (A ⊗[R] C)) (f : A →ₐ[R] B) :
    (∃ z : Spec (CommRingCat.of B) ⟶ tensorCoefficientLocus (I : Set (A ⊗[R] C)),
      z ≫ tensorCoefficientLocusι (I : Set (A ⊗[R] C)) =
        Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
    (∃ q : Spec (CommRingCat.of (B ⊗[R] C)) ⟶
        Spec (CommRingCat.of ((A ⊗[R] C) ⧸ I)),
      q ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) =
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.map f (AlgHom.id R C)).toRingHom)) := by
  rw [affine_factorsThrough_tensorCoefficientLocus_iff,
    affine_factorsThrough_quotient_iff]
  exact (coefficientIdeal_le_ker_iff (I : Set (A ⊗[R] C)) f).symm.trans
    (coefficientIdeal_le_ker_iff_ideal I f)

/-- The product map induced by an algebra map in the first coefficient factor,
written in tensor-spectrum coordinates. -/
def affineProductMap (f : A →ₐ[R] B) :
    pullback (Spec.algebraMap R B) (Spec.algebraMap R C) ⟶
      pullback (Spec.algebraMap R A) (Spec.algebraMap R C) :=
  (pullbackSpecIso R B C).hom ≫
    Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map f (AlgHom.id R C)).toRingHom) ≫
      (pullbackSpecIso R A C).inv

@[reassoc (attr := simp)]
theorem affineProductMap_fst (f : A →ₐ[R] B) :
    affineProductMap (C := C) f ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom f.toRingHom) := by
  simp only [affineProductMap, Category.assoc, pullbackSpecIso_inv_fst]
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := A) (B := C)) ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id R C)).toRingHom =
    CommRingCat.ofHom f.toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := C)) := by
    ext a
    rfl
  rw [h, Spec.map_comp, ← Category.assoc, pullbackSpecIso_hom_fst]

@[reassoc (attr := simp)]
theorem affineProductMap_snd (f : A →ₐ[R] B) :
    affineProductMap (C := C) f ≫ pullback.snd _ _ = pullback.snd _ _ := by
  simp only [affineProductMap, Category.assoc, pullbackSpecIso_inv_snd]
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := A) (B := C)).toRingHom ≫
      CommRingCat.ofHom (Algebra.TensorProduct.map f (AlgHom.id R C)).toRingHom =
    CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := C)).toRingHom := by
    ext c
    simp
  erw [h]
  exact pullbackSpecIso_hom_snd R B C

/-- The original tensor-ideal closed subscheme, placed in the actual affine
fibre product using Mathlib's canonical comparison. -/
def affineTensorQuotientι (I : Ideal (A ⊗[R] C)) :
    Spec (CommRingCat.of ((A ⊗[R] C) ⧸ I)) ⟶
      pullback (Spec.algebraMap R A) (Spec.algebraMap R C) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) ≫
    (pullbackSpecIso R A C).inv

instance affineTensorQuotientι_isClosedImmersion (I : Ideal (A ⊗[R] C)) :
    IsClosedImmersion (affineTensorQuotientι I) := by
  let := IsClosedImmersion.spec_of_quotient_mk
    (R := CommRingCat.of (A ⊗[R] C)) I
  unfold affineTensorQuotientι
  infer_instance

/-- On every affine test algebra the actual coefficient locus represents
factorization of the entire affine product through the tensor-ideal subscheme. -/
theorem affine_coefficientLocus_iff_productFactorization [Module.Projective R C]
    (I : Ideal (A ⊗[R] C)) (f : A →ₐ[R] B) :
    (∃ z : Spec (CommRingCat.of B) ⟶ tensorCoefficientLocus (I : Set (A ⊗[R] C)),
      z ≫ tensorCoefficientLocusι (I : Set (A ⊗[R] C)) =
        Spec.map (CommRingCat.ofHom f.toRingHom)) ↔
    (∃ q : pullback (Spec.algebraMap R B) (Spec.algebraMap R C) ⟶
        Spec (CommRingCat.of ((A ⊗[R] C) ⧸ I)),
      q ≫ affineTensorQuotientι I = affineProductMap (C := C) f) := by
  rw [affine_coefficientLocus_iff_tensorQuotient]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨(pullbackSpecIso R B C).hom ≫ q, ?_⟩
    simp only [affineTensorQuotientι, affineProductMap, Category.assoc]
    rw [← Category.assoc q, hq]
  · rintro ⟨q, hq⟩
    refine ⟨(pullbackSpecIso R B C).inv ≫ q, ?_⟩
    have h := congrArg (fun k ↦
      (pullbackSpecIso R B C).inv ≫ k ≫ (pullbackSpecIso R A C).hom) hq
    simpa only [affineTensorQuotientι, affineProductMap, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc] using h

end Langlands.AlgebraicGeometry
