/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Quotient
import WeilConjectures.RingTheory.Etale.JacobianLift

/-!
# Lifting affine étale schemes across closed immersions

Let `i : Z ⟶ X` be a closed immersion into an affine scheme and `p : V ⟶ Z` étale with `V`
affine. Then `p` is the base change along `i` of an étale morphism `q : U ⟶ X` with `U` affine
(Stacks, Tag 09ZA, first paragraph of the proof, using Tag 04D1).
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

/-- An étale `R ⧸ I`-algebra `B` is the pushout of an étale `R`-algebra along `R ⟶ R ⧸ I`. -/
private theorem exists_isPushout_quotient_of_etale (R : CommRingCat.{u}) (I : Ideal R)
    (B : CommRingCat.{u}) (f : CommRingCat.of (R ⧸ I) ⟶ B) (hf : f.hom.Etale) :
    ∃ (C : CommRingCat.{u}) (g : R ⟶ C) (_ : g.hom.Etale) (a : C ⟶ B),
      IsPushout g (CommRingCat.ofHom (Ideal.Quotient.mk I)) a f := by
  let : Algebra (R ⧸ I) B := f.hom.toAlgebra
  have : Algebra.Etale (R ⧸ I) B := hf
  obtain ⟨C, _, _, hC, e, he⟩ := Algebra.Etale.exists_etale_quotientEquiv I B
  let E : TensorProduct R C (R ⧸ I) ≃+* B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).symm.toRingEquiv.trans e
  let red : C →+* B := e.toRingHom.comp (Ideal.Quotient.mk _)
  have hE (c : C) : E (TensorProduct.tmul R c 1) = red c := by
    dsimp [E, red]
    rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk C I c,
      AlgEquiv.symm_apply_apply]
  have hred (r : R) : red (algebraMap R C r) = f.hom (Ideal.Quotient.mk I r) := he r
  refine ⟨CommRingCat.of C, CommRingCat.ofHom (algebraMap R C),
    RingHom.etale_algebraMap.mpr hC, CommRingCat.ofHom red, ?_⟩
  refine (CommRingCat.isPushout_tensorProduct R C (R ⧸ I)).of_iso
    (f' := CommRingCat.ofHom (algebraMap R C))
    (g' := CommRingCat.ofHom (Ideal.Quotient.mk I))
    (inl' := CommRingCat.ofHom red) (inr' := f)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) E.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp [Ideal.Quotient.algebraMap_eq]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change E (TensorProduct.tmul R c 1) = red c
    exact hE c
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change E (TensorProduct.tmul R (1 : C) (algebraMap R (R ⧸ I) r)) =
      f.hom (Ideal.Quotient.mk I r)
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul, hE]
    exact hred r

/-- **Affine étale schemes lift across closed immersions into affine schemes.** If `X` is
affine, `i: Z ⟶ X` is a closed immersion and `p: V ⟶ Z` is étale with `V` affine, there are an
affine scheme `U`, an étale `q: U ⟶ X` and `a: V ⟶ U` such that `(a, p, q, i)` is a pullback
square. -/
theorem Etale.exists_isPullback_of_isClosedImmersion_of_isAffine {X Z V : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i] (p : V ⟶ Z) [Etale p] [IsAffine V] :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (q : U ⟶ X) (_ : Etale q) (a : V ⟶ U),
      IsPullback a p q i := by
  have : IsClosedImmersion (i ≫ X.isoSpec.hom) := inferInstance
  obtain ⟨I, eZ, hi⟩ := IsClosedImmersion.Spec_iff.mp this
  let eV := V.isoSpec
  obtain ⟨f, hf⟩ := Spec.map_surjective (eV.inv ≫ p ≫ eZ.hom)
  have hp : Etale (Spec.map f) := by
    rw [hf]
    infer_instance
  obtain ⟨C, g, hg, a, H⟩ := exists_isPushout_quotient_of_etale _ I _ f
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hp)
  have : Etale (Spec.map g) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  refine ⟨Spec C, inferInstance, Spec.map g ≫ X.isoSpec.inv, inferInstance,
    eV.hom ≫ Spec.map a, ?_⟩
  apply (isPullback_SpecMap_of_isPushout _ _ _ _ H).of_iso' eV (Iso.refl _) eZ X.isoSpec
  · simp
  · simp [hf]
  · simp
  · exact hi.symm

end AlgebraicGeometry
