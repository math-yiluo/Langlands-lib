/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Limits
import WeilConjectures.RingTheory.EtaleAlgebraLift
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.RingTheory.TensorProduct.Quotient

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- The specified coefficient lift gives a ring pushout along the quotient map. -/
private theorem lift_spec_quotient (R : CommRingCat.{u}) (I : Ideal R)
    (B : CommRingCat.{u}) (f : CommRingCat.of (R ⧸ I) ⟶ B)
    (hf : f.hom.Etale) :
    ∃ (C : CommRingCat.{u}) (g : R ⟶ C) (_ : g.hom.Etale)
      (a : C ⟶ B),
      IsPushout g (CommRingCat.ofHom (Ideal.Quotient.mk I)) a f := by
  let : Algebra (R ⧸ I) B := f.hom.toAlgebra
  have : Algebra.Etale (R ⧸ I) B := hf
  obtain ⟨m, P, L, hC, _, e, he⟩ := Algebra.exists_etale_coefficientLift I B
  let C := L.LiftRing
  let E : TensorProduct R C (R ⧸ I) ≃+* B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot C I).symm.toRingEquiv.trans e
  have hE (c : C) : E (TensorProduct.tmul R c 1) = L.reduction c := by
    dsimp [E]
    rw [← Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk C I c,
      AlgEquiv.symm_apply_apply]
    exact he c
  have hred (r : R) : L.reduction (algebraMap R C r) =
      f.hom (Ideal.Quotient.mk I r) := by
    change L.reduction (Ideal.Quotient.mk L.liftIdeal (MvPolynomial.C r)) = _
    simp [Algebra.SquareJacobianPresentation.CoefficientLift.reduction,
      Algebra.SquareJacobianPresentation.CoefficientLift.polynomialReduction,
      RingHom.algebraMap_toAlgebra]
  refine ⟨CommRingCat.of C, CommRingCat.ofHom (algebraMap R C),
    RingHom.etale_algebraMap.mpr hC, CommRingCat.ofHom L.reduction, ?_⟩
  refine (CommRingCat.isPushout_tensorProduct R C (R ⧸ I)).of_iso
    (f' := CommRingCat.ofHom (algebraMap R C))
    (g' := CommRingCat.ofHom (Ideal.Quotient.mk I))
    (inl' := CommRingCat.ofHom L.reduction) (inr' := f)
    (Iso.refl _) (Iso.refl _) (Iso.refl _) E.toCommRingCatIso ?_ ?_ ?_ ?_
  · simp
  · simp [Ideal.Quotient.algebraMap_eq]
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro c
    change E (TensorProduct.tmul R c 1) = L.reduction c
    exact hE c
  · apply CommRingCat.hom_ext
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    change E (TensorProduct.tmul R (1 : C) (algebraMap R (R ⧸ I) r)) = f.hom (Ideal.Quotient.mk I r)
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    rw [hE]
    exact hred r

/-- Source: Stacks Project, Étale Cohomology, Lemma 59.80.6 (Tag 09ZA),
first sentence of its proof, using Algebra Tag 04D1
(blueprint: theorem-gabber-affine-proper-base-change).

Proof: A closed subscheme of `X = Spec R` is affine, and its ring of global
sections is a quotient `R/I`. Write `V = Spec B`; the morphism `p` corresponds
to an étale `R/I`-algebra `B`. Stacks Tag 04D1 lifts this to an étale
`R`-algebra `C` whose reduction `C/IC` is isomorphic to `B` over `R/I`.
Put `U = Spec C` and let `q` be the map induced by `R → C`.
The tensor-quotient isomorphism identifies `C ⊗[R] (R/I)` with `C/IC`.
The affine fiber-product formula therefore gives an isomorphism
`V ≅ U ×[X] Z` over `Z`. Composing it with the projection to `U` defines
`a`; transporting the canonical pullback square gives `IsPullback a p q i`.
The construction also applies to the zero quotient and empty affine `V`;
no normality, reducedness, or nonemptiness is needed. -/
theorem Etale.exists_affine_lift_of_closedImmersion
    {X Z V : Scheme.{u}} [IsAffine X]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (p : V ⟶ Z) [Etale p] [IsAffine V] :
    ∃ (U : Scheme.{u}) (_ : IsAffine U) (q : U ⟶ X) (_ : Etale q) (a : V ⟶ U),
      IsPullback a p q i := by
  have : IsClosedImmersion (i ≫ X.isoSpec.hom) := inferInstance
  obtain ⟨I, eZ, hi⟩ := IsClosedImmersion.Spec_iff.mp this
  let eV := V.isoSpec
  obtain ⟨f, hf⟩ := Spec.map_surjective (eV.inv ≫ p ≫ eZ.hom)
  have hp : Etale (Spec.map f) := by
    rw [hf]
    infer_instance
  obtain ⟨C, g, hg, a, H⟩ := lift_spec_quotient _ I _ f
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp hp)
  have : Etale (Spec.map g) := (HasRingHomProperty.Spec_iff (P := @Etale)).mpr hg
  refine ⟨Spec C, inferInstance, Spec.map g ≫ X.isoSpec.inv, inferInstance,
    eV.hom ≫ Spec.map a, ?_⟩
  apply (isPullback_SpecMap_of_isPushout _ _ _ _ H).of_iso'
    eV (Iso.refl _) eZ X.isoSpec
  · simp
  · simp [hf]
  · simp
  · exact hi.symm

end AlgebraicGeometry
