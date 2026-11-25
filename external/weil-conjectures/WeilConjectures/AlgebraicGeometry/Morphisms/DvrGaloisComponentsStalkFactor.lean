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
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Basic

public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Limits

import Mathlib.RingTheory.TensorProduct.Finite
import WeilConjectures.RingTheory.DvrGaloisRootTensorReduced
import WeilConjectures.AlgebraicGeometry.Morphisms.ReducedArtinianTensorNormalizationCharts

/-! # Normalized Galois component stalks as integral-closure local factors

## References

* Stacks Project, Tags 09EV, 035H and 0307
-/

@[expose] public section

universe u
open scoped TensorProduct
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- An affine open chart over an affine base identifies structural stalk germs. -/
private theorem affine_chart_stalk_germs
    {A S : CommRingCat.{u}} [Algebra A S] {Y : Scheme.{u}}
    (f : Y ⟶ Spec A) (c : Spec S ⟶ Y) [IsOpenImmersion c]
    (hc : c ≫ f = Spec.map (CommRingCat.ofHom (algebraMap A S)))
    (y : Spec S) :
    ∃ epsilon : Localization.AtPrime y.asIdeal ≃+* Y.presheaf.stalk (c y),
      ∀ s : A, epsilon (algebraMap S (Localization.AtPrime y.asIdeal)
        (algebraMap A S s)) =
        (f.stalkMap (c y)).hom (StructureSheaf.toStalk A (f (c y)) s) := by
  let ec := (asIso (c.stalkMap y)).commRingCatIsoToRingEquiv
  refine ⟨(StructureSheaf.stalkIso S y).toRingEquiv.trans ec.symm, ?_⟩
  intro s
  have hnat : (c.stalkMap y).hom.comp
      ((f.stalkMap (c y)).hom.comp (StructureSheaf.toStalk A (f (c y))).hom) =
      (StructureSheaf.toStalk S y).hom.comp (algebraMap A S) := by
    calc
      _ = ((c ≫ f).stalkMap y).hom.comp
          (StructureSheaf.toStalk A ((c ≫ f) y)).hom := by
        rw [Hom.stalkMap_comp]
        rfl
      _ = _ := by
        rw [hc]
        exact congrArg CommRingCat.Hom.hom
          (stalkMap_toStalk (CommRingCat.ofHom (algebraMap A S)) y)
  apply ec.injective
  change ec (ec.symm ((StructureSheaf.stalkIso S y)
      (algebraMap S (Localization.AtPrime y.asIdeal) (algebraMap A S s)))) = _
  rw [ec.apply_symm_apply]
  exact ((StructureSheaf.stalkIso S y).commutes (algebraMap A S s)).trans
    (RingHom.congr_fun hnat s).symm

set_option backward.isDefEq.respectTransparency false in
/-- Identify the actual stalk and every structural germ with a generic field factor. -/
theorem dvr_galois_components_stalk_factor
    (B : CommRingCat.{u}) [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hnpos : 0 < n)
    (r : ℕ) (E : Fin r → Type u) [∀ i, Field (E i)]
    [∀ i, Algebra (FractionRing B) (E i)]
    (hE : ∀ i, FiniteDimensional (FractionRing B) (E i) ∧
      IsGalois (FractionRing B) (E i))
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
    letI : ∀ i, Algebra B (E i) := fun i ↦
      ((algebraMap (FractionRing B) (E i)).comp
        (algebraMap B (FractionRing B))).toAlgebra
    ∃ (i : Fin r) (P : Ideal (E i ⊗[B] A)) (hP : P.IsMaximal),
    letI := hP
    let F := (E i ⊗[B] A) ⧸ P
    let alpha : A →+* F := (Ideal.Quotient.mk P).comp
      (Algebra.TensorProduct.includeRight : A →ₐ[B] E i ⊗[B] A).toRingHom
    letI := alpha.toAlgebra
    let S := integralClosure A F
    ∃ (Q : Ideal S) (hQ : Q.IsPrime),
    letI := hQ
    Q.comap (algebraMap A S) = Ideal.span
      {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} ∧
    ∃ (epsilon : Localization.AtPrime Q ≃+* a.normalization.presheaf.stalk x),
      ∀ s : A, epsilon (algebraMap S (Localization.AtPrime Q) (algebraMap A S s)) =
        (a.fromNormalization.stalkMap x).hom
          (StructureSheaf.toStalk A (a.fromNormalization x) s) := by
  dsimp only
  intro hqc hqs
  let := hqc
  let := hqs
  intro x hx
  let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
  let (i : Fin r) : Algebra B (E i) :=
    ((algebraMap (FractionRing B) (E i)).comp
      (algebraMap B (FractionRing B))).toAlgebra
  have hD (i : Fin r) :
      IsArtinianRing (E i ⊗[B] A) ∧ _root_.IsReduced (E i ⊗[B] A) := by
    have : Module.Finite B A :=
      (Polynomial.monic_X_pow_sub_C pi (Nat.ne_of_gt hnpos)).finite_adjoinRoot
    exact ⟨IsArtinianRing.of_finite (E i) _,
      RingTheory.dvr_galois_root_tensor_reduced B pi hpi n hnpos (E i) (hE i)⟩
  have heB : e.hom ≫ Sigma.desc (fun i : Fin r ↦
      Spec.map (CommRingCat.ofHom (algebraMap B (E i)))) =
      p ≫ Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))) := by
    rw [← he, Category.assoc]
    congr 1
    apply Sigma.hom_ext
    intro i
    simp only [Sigma.ι_comp_desc_assoc, Sigma.ι_comp_desc]
    rw [← Spec.map_comp]
    rfl
  have hcharts :=
    reduced_artinian_tensor_normalization_charts B (CommRingCat.of A) r E hD X
      (p ≫ Spec.map (CommRingCat.ofHom (algebraMap B (FractionRing B))))
      e heB hqc hqs x
  obtain ⟨i, P, hP, c, hc, hcA, y, hy⟩ := hcharts
  let := hP
  let F := (E i ⊗[B] A) ⧸ P
  let alpha : A →+* F := (Ideal.Quotient.mk P).comp
    (Algebra.TensorProduct.includeRight : A →ₐ[B] E i ⊗[B] A).toRingHom
  let := alpha.toAlgebra
  let S := integralClosure A F
  let := hc
  subst x
  refine ⟨i, P, hP, y.asIdeal, y.isPrime, ?_, ?_⟩
  · have hpoint : (c ≫ _ ) y = _ := congrArg (fun f ↦ f y) hcA
    rw [← hx]
    exact (congrArg PrimeSpectrum.asIdeal hpoint).symm
  · exact affine_chart_stalk_germs _ c hcA y

end AlgebraicGeometry.Scheme
