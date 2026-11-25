/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import WeilConjectures.Mathlib.RingTheory.ReesAlgebra

import WeilConjectures.Mathlib.RingTheory.Smooth.StandardSmooth

set_option autoImplicit false

open scoped TensorProduct LaurentPolynomial
open MvPolynomial
open CategoryTheory

universe u v

/-!
# Étale deformation chart and its smooth projection
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-geometry/_section.md
(blueprint: lem-pur-dnc-etale-rees-chart)

The helpers use the published extended-Rees algebra and origin-chart API.

## Main definitions

- `AlgebraicGeometry.etaleReesChartMap`: the polynomial chart map to the mapped Rees algebra.
- `AlgebraicGeometry.etaleReesBaseMap`: the affine-line base map.
- `AlgebraicGeometry.etaleReesTensorMap`: the canonical tensor map.

## Main statements

- `AlgebraicGeometry.etale_rees_chart`: polynomial compatibility, canonical tensor
  bijectivity, étaleness, and smoothness of relative dimension `d`.
-/

@[expose] public section

namespace AlgebraicGeometry

private theorem etale_comp {B C D : Type*} [CommRing B] [CommRing C] [CommRing D]
    (f : B →+* C) (g : C →+* D) (hf : f.Etale) (hg : g.Etale) :
    (g.comp f).Etale := by
  algebraize [f, g, g.comp f]
  exact Algebra.Etale.comp B C D

/--
The canonical chart map from the polynomial presentation of the origin chart to the
extended Rees algebra after the étale base change.
Source: blueprint `chap-Smooth-purity`, clause (2), coordinates `u_i = x_i/t`
(blueprint: lem-pur-dnc-etale-rees-chart).
-/
noncomputable def etaleReesChartMap
    (A : Type u) (R : Type v) [CommRing A] [CommRing R] (d : ℕ)
    [Algebra (MvPolynomial (Fin d) A) R] :
    MvPolynomial (Fin d) (Polynomial A) →+*
      ((Ideal.mvPolynomialOrigin A (Fin d)).map
        (algebraMap (MvPolynomial (Fin d) A) R)).extendedReesAlgebra :=
  ((Ideal.mvPolynomialOrigin A (Fin d)).extendedReesAlgebraAlgHom R).toRingHom.comp
    (Ideal.mvPolynomialExtendedReesAlgebraEquiv A (Fin d)).toRingHom

/--
The affine-line structure map in the polynomial presentation of the origin chart.
Source: blueprint `chap-Smooth-purity`, clause (2), affine-space projection
(blueprint: lem-pur-dnc-etale-rees-chart).
-/
noncomputable def etaleReesBaseMap
    (A : Type u) [CommRing A] (d : ℕ) :
    Polynomial A →+* MvPolynomial (Fin d) (Polynomial A) :=
  MvPolynomial.C

/--
The canonical tensor map induced by coefficientwise Laurent-polynomial functoriality
of the extended-Rees algebra.  Its data is the tensor-product lift of the existing
`Ideal.extendedReesAlgebraAlgHom`.
Source: blueprint `chap-Smooth-purity`, clause (2), flat tensor identification
(blueprint: lem-pur-dnc-etale-rees-chart).
-/
noncomputable def etaleReesTensorMap
    (A : Type u) (R : Type v) [CommRing A] [CommRing R] (d : ℕ)
    [Algebra (MvPolynomial (Fin d) A) R] :
    R ⊗[MvPolynomial (Fin d) A] (Ideal.mvPolynomialOrigin A (Fin d)).extendedReesAlgebra
      →ₐ[R]
        ((Ideal.mvPolynomialOrigin A (Fin d)).map
          (algebraMap (MvPolynomial (Fin d) A) R)).extendedReesAlgebra :=
  Algebra.TensorProduct.lift (Algebra.ofId R _)
    ((Ideal.mvPolynomialOrigin A (Fin d)).extendedReesAlgebraAlgHom R)
    (fun _ _ ↦ Commute.all _ _)

/-- The canonical universe-lifted ring map used to form the affine scheme morphism.
The `ULift` transport puts the source and target rings in the common universe
`max u v`, preserving the underlying map for arbitrary ring universes.
Source: blueprint `chap-Smooth-purity`, clause (2), affine spectra
(blueprint: lem-pur-dnc-etale-rees-chart). -/
noncomputable def etaleReesChartSchemeMap
    (A : Type u) (R : Type v) [CommRing A] [CommRing R] (d : ℕ)
    [Algebra (MvPolynomial (Fin d) A) R] :
    ULift.{v} (MvPolynomial (Fin d) (Polynomial A)) →+*
      ULift.{u} ((Ideal.mvPolynomialOrigin A (Fin d)).map
        (algebraMap (MvPolynomial (Fin d) A) R)).extendedReesAlgebra :=
  RingHom.ulift.{v, u} (etaleReesChartMap A R d)

/-- The universe-lifted affine-line base map, with source and target in
`max u v` so it composes with `etaleReesChartSchemeMap`. -/
noncomputable def etaleReesBaseSchemeMap
    (A : Type u) [CommRing A] (_R : Type v) (d : ℕ) :
    ULift.{v} (Polynomial A) →+* ULift.{v} (MvPolynomial (Fin d) (Polynomial A)) :=
  RingHom.ulift.{v, v} (etaleReesBaseMap A d)

/--
Source: literature/blueprint/main-20261015/blueprint/sec-smooth-purity/sk-lem-geometry/_section.md,
clause (2), local deformation algebra and étale base change.
The scheme notions are `def-weil-etale-morphism`, `def-weil-affine-spectrum`,
`def-sbc-affine-space`, and `def-sbc-smooth-morphisms`.
The proof proceeds as follows. (1) The existing equivalence
`Ideal.mvPolynomialExtendedReesAlgebraEquiv` identifies the origin extended-Rees
algebra with `A[t,u_1, ..., u_d]`, sending `x_i` to `t u_i`. (2) The étale hypothesis
is flat, so tensoring the inclusion into Laurent polynomials remains injective; this
is `lem-weil-pbc-flat-ring-map-iff-flat-affine`, `def-weil-pbc-flat-ring-map`, and
`lem-weil-pbc-flat-tensor-exact`. (3) The tensor-product universal property
`lem-weil-pbc-algebra-tensor-pushout-universal-property` identifies the image with
`R[t,I/t]`; the canonical map is `etaleReesTensorMap`, and the displayed equation
records its coefficientwise Laurent action. (4) The affine tensor fibre-product
identification `lem-weil-pbc-fibre-product-affine-spectra` and étale base-change
statement `lem-weil-pbc-etale-scheme-base-change` make `etaleReesChartMap` étale.
(5) The affine-space smoothness statement `sbc-lem-affine-space-smooth`, the
étale relative-dimension-zero comparison
`lem-weil-pbc-etale-smooth-zero-dimensional-fibres`, and composition permanence
`lem-sbc-smooth-relative-dimension-permanence` give smooth relative dimension `d`.
(blueprint: lem-pur-dnc-etale-rees-chart).
-/
theorem etale_rees_chart
    (A : Type u) (R : Type v) [CommRing A] [CommRing R] (d : ℕ)
    [Algebra (MvPolynomial (Fin d) A) R]
    (he : (algebraMap (MvPolynomial (Fin d) A) R).Etale) :
    ((Ideal.mvPolynomialExtendedReesAlgebraEquiv A (Fin d)).toRingHom.comp
        (MvPolynomial.C : Polynomial A →+* MvPolynomial (Fin d) (Polynomial A)) =
      (Ideal.mvPolynomialOrigin A (Fin d)).toExtendedReesAlgebra.comp
        (Polynomial.mapRingHom (MvPolynomial.C : A →+* MvPolynomial (Fin d) A))) ∧
      (∀ i : Fin d,
        (Ideal.mvPolynomialExtendedReesAlgebraEquiv A (Fin d)).symm
            (algebraMap (MvPolynomial (Fin d) A)
              (Ideal.mvPolynomialOrigin A (Fin d)).extendedReesAlgebra (MvPolynomial.X i)) =
          MvPolynomial.C Polynomial.X * MvPolynomial.X i) ∧
      Function.Bijective (etaleReesTensorMap A R d) ∧
      (∀ (r : R)
        (z : (Ideal.mvPolynomialOrigin A (Fin d)).extendedReesAlgebra),
        ((etaleReesTensorMap A R d) (r ⊗ₜ z) : LaurentPolynomial R) =
          LaurentPolynomial.C r *
            LaurentPolynomial.mapRingHom (algebraMap (MvPolynomial (Fin d) A) R)
              (z : LaurentPolynomial (MvPolynomial (Fin d) A))) ∧
      AlgebraicGeometry.Etale
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (etaleReesChartSchemeMap A R d))) ∧
      AlgebraicGeometry.SmoothOfRelativeDimension d
        (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (etaleReesChartSchemeMap A R d)) ≫
          AlgebraicGeometry.Spec.map (CommRingCat.ofHom (etaleReesBaseSchemeMap A R d))) := by
  have hEtale : Algebra.Etale (MvPolynomial (Fin d) A) R :=
    RingHom.etale_algebraMap.mp he
  let J := Ideal.mvPolynomialOrigin A (Fin d)
  let E := J.extendedReesAlgebra
  let D := (J.map (algebraMap (MvPolynomial (Fin d) A) R)).extendedReesAlgebra
  have hTensor : Function.Bijective (etaleReesTensorMap A R d) := by
    have h := J.isBaseChange_extendedReesAlgebraAlgHom R
    have hmap : (etaleReesTensorMap A R d).toLinearMap = h.equiv.toLinearMap := by
      apply LinearMap.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul r z =>
        change etaleReesTensorMap A R d (r ⊗ₜ z) = h.equiv (r ⊗ₜ z)
        rw [IsBaseChange.equiv_tmul]
        simp [etaleReesTensorMap, Algebra.smul_def, J]
      | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy
    change Function.Bijective (etaleReesTensorMap A R d).toLinearMap
    rw [hmap]
    exact h.equiv.bijective
  have hRees : (algebraMap E D).Etale := by
    have : Algebra.IsPushout (MvPolynomial (Fin d) A) E R D :=
      Algebra.IsPushout.symm inferInstance
    have : Algebra.Etale E D := Algebra.Etale.of_equiv
      (Algebra.IsPushout.equiv (MvPolynomial (Fin d) A) E R D)
    exact RingHom.etale_algebraMap.mpr this
  have hChart : (etaleReesChartMap A R d).Etale :=
    etale_comp _ _ (RingHom.Etale.of_bijective
      (Ideal.mvPolynomialExtendedReesAlgebraEquiv A (Fin d)).bijective) hRees
  have hLift : (etaleReesChartSchemeMap A R d).Etale := by
    exact etale_comp _ _
      (etale_comp _ _ (RingHom.Etale.of_bijective ULift.ringEquiv.bijective) hChart)
      (RingHom.Etale.of_bijective ULift.ringEquiv.symm.bijective)
  have hScheme : Etale (Spec.map (CommRingCat.ofHom (etaleReesChartSchemeMap A R d))) :=
    HasRingHomProperty.Spec_iff.mpr hLift
  refine ⟨Ideal.mvPolynomialExtendedReesAlgebraEquiv_comp_C A (Fin d), ?_,
    hTensor, ?_, hScheme, ?_⟩
  · intro i
    apply (Ideal.mvPolynomialExtendedReesAlgebraEquiv A (Fin d)).injective
    apply Subtype.ext
    rw [RingEquiv.apply_symm_apply]
    change LaurentPolynomial.C (MvPolynomial.X i) =
      Ideal.mvPolynomialToLaurent A (Fin d) (MvPolynomial.C Polynomial.X * MvPolynomial.X i)
    rw [map_mul, Ideal.mvPolynomialToLaurent_C, Ideal.mvPolynomialToLaurent_X,
      Polynomial.map_X, Polynomial.toLaurent_X]
    simp
  · intro r z
    simp [etaleReesTensorMap, Ideal.coe_extendedReesAlgebraAlgHom,
      ← LaurentPolynomial.C_eq_algebraMap]
  · have hp : RingHom.IsStandardSmoothOfRelativeDimension d
        (etaleReesBaseMap A d) := by
      simpa [etaleReesBaseMap] using
        (RingHom.isStandardSmoothOfRelativeDimension_algebraMap
          (R := Polynomial A) (S := MvPolynomial (Fin d) (Polynomial A))
          (n := Nat.card (Fin d))).mpr
          (MvPolynomial.isStandardSmoothOfRelativeDimension _ _)
    have hpl : RingHom.IsStandardSmoothOfRelativeDimension d
        (etaleReesBaseSchemeMap A R d) := by
      have h₁ := hp.comp
        (RingHom.IsStandardSmoothOfRelativeDimension.equiv
          (ULift.ringEquiv : ULift.{v} (Polynomial A) ≃+* Polynomial A))
      have h₂ := (RingHom.IsStandardSmoothOfRelativeDimension.equiv
        (ULift.ringEquiv.symm : MvPolynomial (Fin d) (Polynomial A) ≃+*
          ULift.{v} (MvPolynomial (Fin d) (Polynomial A)))).comp h₁
      simp only [Nat.add_zero, Nat.zero_add] at h₂
      convert h₂ using 1
      ext x
      rfl
    have hps : SmoothOfRelativeDimension d
        (Spec.map (CommRingCat.ofHom (etaleReesBaseSchemeMap A R d))) := by
      apply HasRingHomProperty.Spec_iff.mpr
      exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hpl
    have hc := smoothOfRelativeDimension_comp (n := 0) (m := d)
      (Spec.map (CommRingCat.ofHom (etaleReesChartSchemeMap A R d)))
      (Spec.map (CommRingCat.ofHom (etaleReesBaseSchemeMap A R d)))
      (hf := inferInstance) (hg := hps)
    simpa only [Nat.zero_add] using hc

end AlgebraicGeometry
