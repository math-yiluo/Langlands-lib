/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits

import WeilConjectures.AlgebraicGeometry.Morphisms.DvrGaloisComponentsStalkFactor
import WeilConjectures.RingTheory.DvrGaloisRootFactorUniformizer

/-! # The tame root germ is not in the square of the maximal ideal

## References

* Stacks Project, Tags 09EV, 09EB, 0BRM, 09E7 and 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem root_factor_ne_zero
    (B : Type u) [CommRing B] [IsDomain B] (pi : B) (hpi : pi ≠ 0) (n : ℕ) (hn : 0 < n)
    (E : Type u) [Field E] [Algebra (FractionRing B) E] :
    letI : Algebra B E :=
      ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    let D := TensorProduct B E A
    ∀ (P : Ideal D) (hP : P.IsMaximal),
    letI := hP
    let F := D ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
    letI := alpha.toAlgebra
    let S := integralClosure A F
    ∀ (Q : Ideal S) (hQ : Q.IsPrime),
    letI := hQ
    algebraMap S (Localization.AtPrime Q)
      (algebraMap A S
        (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi))) ≠ 0 := by
  dsimp only
  let : Algebra B E :=
    ((algebraMap (FractionRing B) E).comp (algebraMap B (FractionRing B))).toAlgebra
  intro P hP
  let := hP
  intro Q hQ
  let := hQ
  let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
  let D := TensorProduct B E A
  let F := D ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] D).toRingHom
  let : Algebra A F := alpha.toAlgebra
  let S := integralClosure A F
  let t : A := AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
  have hpiE : algebraMap B E pi ≠ 0 := by
    change algebraMap (FractionRing B) E (algebraMap B (FractionRing B) pi) ≠ 0
    simpa only [map_zero] using (algebraMap (FractionRing B) E).injective.ne
      ((IsFractionRing.injective B (FractionRing B)).ne hpi)
  have hpiF : IsUnit (alpha (algebraMap B A pi)) := by
    have h := (isUnit_iff_ne_zero.mpr hpiE).map
      ((Ideal.Quotient.mk P).comp (Algebra.TensorProduct.includeLeftRingHom (R := B)))
    convert h using 1
    exact congrArg (fun f : B →+* D ↦ Ideal.Quotient.mk P (f pi))
      Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap.symm
  have ht : t ^ n = algebraMap B A pi := by
    rw [AdjoinRoot.algebraMap_eq]
    have he := AdjoinRoot.eval₂_root
      ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, AdjoinRoot.algebraMap_eq] using he
  have htF : alpha t ≠ 0 := by
    intro h
    have hpow : alpha (algebraMap B A pi) = 0 := by
      rw [← ht, map_pow, h]
      exact zero_pow hn.ne'
    exact hpiF.ne_zero hpow
  have htS : algebraMap A S t ≠ 0 := by
    intro h
    apply htF
    exact congrArg Subtype.val h
  simpa only [map_zero] using
    (FaithfulSMul.algebraMap_injective S (Localization.AtPrime Q)).ne htS

private theorem generator_not_mem_square_of_equiv
    {D C : Type u} [CommRing D] [CommRing C] [IsDomain D]
    [IsLocalRing D] [IsLocalRing C] (epsilon : D ≃+* C) (t : D)
    (ht : t ≠ 0) (hm : IsLocalRing.maximalIdeal D = Ideal.span {t}) :
    epsilon t ∉ IsLocalRing.maximalIdeal C * IsLocalRing.maximalIdeal C := by
  have hspan : IsLocalRing.maximalIdeal C = Ideal.span {epsilon t} := by
    rw [← IsLocalRing.map_ringEquiv_maximalIdeal epsilon, hm, Ideal.map_span,
      Set.image_singleton]
  have htau : epsilon t ≠ 0 := by simpa using ht
  have : IsDomain C := epsilon.toMulEquiv.isDomain_iff.mp inferInstance
  intro h
  have h' : epsilon t ∈ Ideal.span {epsilon t} * IsLocalRing.maximalIdeal C := by
    rwa [← hspan]
  obtain ⟨z, hz, heq⟩ := Ideal.mem_span_singleton_mul.mp h'
  have hz1 : z = 1 := mul_left_cancel₀ htau (heq.trans (mul_one _).symm)
  exact (IsLocalRing.maximalIdeal.isMaximal C).ne_top
    ((IsLocalRing.maximalIdeal C).eq_top_of_isUnit_mem (hz1 ▸ hz) isUnit_one)

/-- The tame root germ has nonzero class modulo the normalized maximal-ideal square. -/
theorem dvr_galois_components_root_not_mem_square
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (hn : IsUnit (n : B))
    (r : ℕ) (E : Fin r → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (FractionRing B) (E i)]
    (hE : ∀ i, FiniteDimensional (FractionRing B) (E i) ∧
      IsGalois (FractionRing B) (E i) ∧ Module.finrank (FractionRing B) (E i) ∣ n)
    (X : Scheme.{u}) (p : X ⟶ Spec (CommRingCat.of (FractionRing B)))
    (e : X ≅ ∐ fun i : Fin r ↦ Spec (CommRingCat.of (E i)))
    (he : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing B) (E i)))) = p) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
    let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
    let a := pullback.snd (p ≫ j) q
    ∀ (hqc : QuasiCompact a) (hqs : QuasiSeparated a),
    letI := hqc
    letI := hqs
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} →
      let C := a.normalization.presheaf.stalk x
      let tau := (a.fromNormalization.stalkMap x).hom
        (StructureSheaf.toStalk A (a.fromNormalization x)
          (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)))
      let m := IsLocalRing.maximalIdeal C
      tau ∉ m * m := by
  dsimp only
  intro hqc hqs
  let := hqc
  let := hqs
  intro x hx
  let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
  let q := Spec.map (CommRingCat.ofHom (algebraMap B A))
  let j := Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B)))
  let a := pullback.snd (p ≫ j) q
  let C := a.normalization.presheaf.stalk x
  let tau := (a.fromNormalization.stalkMap x).hom
    (StructureSheaf.toStalk A (a.fromNormalization x)
      (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)))
  let m := IsLocalRing.maximalIdeal C
  obtain ⟨i, P, hP, Q, hQ, hcontract, epsilon, hepsilon⟩ :=
    dvr_galois_components_stalk_factor B pi hpi n hnpos r E
      (fun i ↦ ⟨(hE i).1, (hE i).2.1⟩) X p e he hqc hqs x hx
  let : Algebra B (E i) :=
    ((algebraMap (FractionRing B) (E i)).comp
      (algebraMap B (FractionRing B))).toAlgebra
  let := hP
  let F := (TensorProduct B (E i) A) ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] TensorProduct B (E i) A).toRingHom
  let := alpha.toAlgebra
  let S := integralClosure A F
  let := hQ
  let t := algebraMap S (Localization.AtPrime Q)
    (algebraMap A S
      (AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)))
  have hm := RingTheory.dvr_galois_root_factor_uniformizer
    B pi hpi n hnpos hn (E i) (hE i) P hP Q hQ hcontract
  have ht := root_factor_ne_zero B pi hpi.ne_zero n hnpos (E i) P hP Q hQ
  have het : epsilon t = tau := hepsilon _
  change tau ∉ m * m
  rw [← het]
  exact generator_not_mem_square_of_equiv epsilon t ht hm

end AlgebraicGeometry.Scheme
