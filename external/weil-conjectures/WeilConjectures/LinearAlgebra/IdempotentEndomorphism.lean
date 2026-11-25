/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

/-!
# Idempotent endomorphisms of finite free modules

This file collects facts about idempotent endomorphisms `p` of `Rⁿ` used in the proof that
finite projective modules lift along henselian pairs (Stacks, Lemma 15.11.8, Tag 07M5):

* over a field, the characteristic polynomial of `p` is `(X - 1) ^ r * X ^ (n - r)` where `r` is
  the rank of `p`; over any commutative ring the characteristic polynomial of an idempotent
  matrix divides `(X - X²) ^ n`;
* the image of `p` is a finite projective direct summand, and its formation commutes with base
  change;
* an idempotent endomorphism of `(A ⧸ I)ⁿ` has an integral commutative model: an integral
  `A`-algebra `B`, an `A`-algebra map `B → Mₙ(A)` and `y ∈ B` idempotent modulo `IB` whose image
  reduces to the matrix of `p`.

## Main statements

- `LinearMap.charpoly_eq_of_isIdempotentElem`
- `Matrix.charpoly_dvd_X_sub_X_sq_pow_of_isIdempotentElem`
- `IsIdempotentElem.range_projective_and_baseChange`
- `Ideal.exists_isIntegral_matrix_model_of_isIdempotentElem`
-/

@[expose] public section

open Polynomial LinearMap TensorProduct

universe u

/-- Over a field, the characteristic polynomial of an idempotent endomorphism `p` of `kⁿ` is
`(X - 1) ^ r * X ^ (n - r)` with `r = dim (Im p)` (computed for `p` or for its matrix); in
particular it divides `X ^ n * (X - 1) ^ n`.
(blueprint: `lem-weil-pbc-idempotent-endomorphism-charpoly-field`) -/
theorem LinearMap.charpoly_eq_of_isIdempotentElem {k : Type*} [Field k] {n : ℕ}
    (p : Module.End k (Fin n → k)) (hp : IsIdempotentElem p) :
    p.charpoly = (X - 1) ^ Module.finrank k (range p) * X ^ (n - Module.finrank k (range p)) ∧
    (toMatrix' p).charpoly =
      (X - 1) ^ Module.finrank k (range p) * X ^ (n - Module.finrank k (range p)) ∧
    p.charpoly ∣ X ^ n * (X - 1) ^ n := by
  have hc := hp.isCompl
  let e := Submodule.prodEquivOfIsCompl _ _ hc
  have key : e.symm.conj p = (1 : Module.End k (range p)).prodMap
      (0 : Module.End k (ker p)) := by
    refine LinearMap.ext fun ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ ↦ ?_
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.symm_apply_eq]
    rw [mem_ker] at hy
    have hx' : p x = x := hp.mem_range_iff.mp hx
    simp [e, Submodule.coe_prodEquivOfIsCompl', hx', hy]
  have hrk := LinearMap.finrank_range_add_finrank_ker p
  simp only [Module.finrank_fin_fun] at hrk
  have h1 : p.charpoly = (X - 1) ^ Module.finrank k (range p) *
      X ^ (n - Module.finrank k (range p)) := by
    rw [← LinearEquiv.charpoly_conj e.symm, key, charpoly_prodMap, charpoly_one, charpoly_zero]
    congr 2
    omega
  have h2 : (toMatrix' p).charpoly = p.charpoly := by
    rw [← LinearMap.toMatrix_eq_toMatrix', LinearMap.charpoly_toMatrix]
  refine ⟨h1, h2.trans h1, ?_⟩
  rw [h1, mul_comm]
  exact mul_dvd_mul (pow_dvd_pow _ (by omega)) (pow_dvd_pow _ (by omega))

/-- The characteristic polynomial of an idempotent square matrix over a commutative ring divides
`(X - X ^ 2) ^ n`. -/
theorem Matrix.charpoly_dvd_X_sub_X_sq_pow_of_isIdempotentElem {R : Type*} [CommRing R]
    {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n R} (hM : IsIdempotentElem M) :
    M.charpoly ∣ (X - X ^ 2) ^ Fintype.card n := by
  let N : Matrix n n R[X] := M.map C
  have hN : N * N = N := by
    simp only [N, ← Matrix.map_mul, hM.eq]
  have key : charmatrix M * (1 - Matrix.scalar n (X : R[X]) - N) =
      Matrix.scalar n (X - X ^ 2 : R[X]) := by
    have hc : Matrix.scalar n (X : R[X]) * N = N * Matrix.scalar n (X : R[X]) :=
      (Matrix.scalar_commute _ (fun _ ↦ Commute.all _ _) _)
    rw [show charmatrix M = Matrix.scalar n (X : R[X]) - N from rfl, map_sub, pow_two, map_mul]
    simp only [mul_sub, sub_mul, mul_one, hN, hc]
    abel
  refine ⟨(1 - Matrix.scalar n (X : R[X]) - N).det, ?_⟩
  rw [Matrix.charpoly, ← Matrix.det_mul, key]
  simp [Matrix.scalar_apply, Matrix.det_diagonal]

/-- Let `p` be an idempotent endomorphism of `Rⁿ`. (i) `Rⁿ = Im p ⊕ Im (1 - p)` with
`Im (1 - p) = ker p`, and `Im p` is a finite projective `R`-module. (ii) For an `R`-algebra `S`,
the endomorphism `p_S` of `Sⁿ` with the matrix of `p` mapped to `S` is idempotent, and the
`S`-linear map `S ⊗[R] Im p → Sⁿ`, `s ⊗ v ↦ s • v`, is injective with image `Im p_S`.
(blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem IsIdempotentElem.range_projective_and_baseChange {R : Type*} [CommRing R] {n : ℕ}
    (p : Module.End R (Fin n → R))
    (hp : IsIdempotentElem p) (S : Type*) [CommRing S] [Algebra R S] :
    (IsCompl (range p) (ker p) ∧ range (1 - p) = ker p ∧
      Module.Projective R (range p) ∧ Module.Finite R (range p)) ∧
    (IsIdempotentElem (Matrix.toLin' ((toMatrix' p).map (algebraMap R S))) ∧
      ∃ φ : S ⊗[R] range p →ₗ[S] (Fin n → S),
        (∀ (s : S) (v : range p), φ (s ⊗ₜ v) = s • (algebraMap R S ∘ (v : Fin n → R))) ∧
        Function.Injective φ ∧
        range φ = range (Matrix.toLin' ((toMatrix' p).map (algebraMap R S)))) := by
  have hri : p.rangeRestrict ∘ₗ (range p).subtype = LinearMap.id := by
    ext ⟨x, hx⟩
    simp [hp.mem_range_iff.mp hx]
  refine ⟨⟨hp.isCompl, hp.ker_eq_range_one_sub.symm,
    Module.Projective.of_split _ _ hri, Module.Finite.of_surjective _ p.surjective_rangeRestrict⟩,
    ?_, ?_⟩
  · exact (hp.map (LinearMap.toMatrixAlgEquiv' (R := R))).map (RingHom.mapMatrix (algebraMap R S))
      |>.map (Matrix.toLinAlgEquiv' (R := S))
  · let ψ := (piScalarRight R S S (Fin n)).toLinearMap
    have hcomm : Matrix.toLin' ((toMatrix' p).map (algebraMap R S)) ∘ₗ ψ =
        ψ ∘ₗ p.baseChange S := by
      refine LinearMap.ext fun x ↦ x.inductionOn (fun s v ↦ ?_) (fun a b ha hb ↦ by
        rw [map_add, map_add, ha, hb])
      conv_rhs => rw [← Matrix.toLin'_toMatrix' p]
      ext i
      simp only [ψ, LinearMap.comp_apply, LinearEquiv.coe_coe, piScalarRight_apply,
        piScalarRightHom_tmul, LinearMap.baseChange_tmul, Matrix.toLin'_apply]
      simp [Matrix.mulVec, dotProduct, Finset.sum_mul, Algebra.smul_def, mul_assoc]
    refine ⟨ψ ∘ₗ (range p).subtype.baseChange S, fun s v ↦ ?_, ?_, ?_⟩
    · ext i
      simp [ψ, Algebra.smul_def, mul_comm]
    · refine (piScalarRight R S S (Fin n)).injective.comp ?_
      refine Function.LeftInverse.injective (g := p.rangeRestrict.baseChange S) fun x ↦ ?_
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hri, LinearMap.baseChange_id,
        LinearMap.id_apply]
    · have hp' : p = (range p).subtype ∘ₗ p.rangeRestrict := rfl
      have hs : Function.Surjective (p.rangeRestrict.baseChange S) :=
        LinearMap.lTensor_surjective _ p.surjective_rangeRestrict
      rw [LinearMap.range_comp, ← LinearMap.range_comp_of_range_eq_top _ (range_eq_top.mpr hs),
        ← LinearMap.baseChange_comp, ← hp', ← LinearMap.range_comp, ← hcomm,
        LinearMap.range_comp_of_range_eq_top _
          (range_eq_top.mpr (piScalarRight R S S (Fin n)).surjective)]

/-- An idempotent endomorphism `p̄` of `(A ⧸ I)ⁿ` has an integral commutative model: there are
an integral commutative `A`-algebra `B`, an `A`-algebra map `ψ : B → Mₙ(A)` and `y ∈ B` such that
`y mod IB` is idempotent and `ψ y` reduces modulo `I` to the matrix of `p̄`.
(blueprint: `theorem-finite-etale-covers-proper-henselian--2`) -/
theorem Ideal.exists_isIntegral_matrix_model_of_isIdempotentElem {A : Type u} [CommRing A]
    (I : Ideal A) {n : ℕ}
    (p : Module.End (A ⧸ I) (Fin n → A ⧸ I)) (hp : IsIdempotentElem p) :
    ∃ (B : Type u) (_ : CommRing B) (_ : Algebra A B) (_ : Algebra.IsIntegral A B)
      (ψ : B →ₐ[A] Matrix (Fin n) (Fin n) A) (y : B),
      IsIdempotentElem (Ideal.Quotient.mk (I.map (algebraMap A B)) y) ∧
      (ψ y).map (Ideal.Quotient.mk I) = LinearMap.toMatrix' p := by
  set M := LinearMap.toMatrix' p
  have hM : IsIdempotentElem M := hp.map LinearMap.toMatrixAlgEquiv'
  obtain ⟨X₀, hX₀⟩ : ∃ X₀ : Matrix (Fin n) (Fin n) A, X₀.map (Ideal.Quotient.mk I) = M :=
    ⟨M.map (Function.surjInv Ideal.Quotient.mk_surjective),
      by ext; simp [Function.surjInv_eq Ideal.Quotient.mk_surjective]⟩
  set f := X₀.charpoly
  have hf : f.Monic := X₀.charpoly_monic
  have : Module.Finite A (AdjoinRoot f) := hf.finite_adjoinRoot
  let ψ : AdjoinRoot f →ₐ[A] Matrix (Fin n) (Fin n) A :=
    Ideal.Quotient.liftₐ (Ideal.span {f}) (aeval X₀) fun a ha ↦ by
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.mp ha
      rw [map_mul, X₀.aeval_self_charpoly, mul_zero]
  set x := AdjoinRoot.root f
  set N := n + 1
  have hψx : ψ x = X₀ := by
    change Ideal.Quotient.liftₐ _ _ _ (Ideal.Quotient.mk _ X) = X₀
    exact aeval_X X₀
  refine ⟨AdjoinRoot f, inferInstance, inferInstance, inferInstance, ψ, 1 - (1 - x ^ N) ^ N,
    ?_, ?_⟩
  · rw [map_sub, map_one, map_pow, map_sub, map_one, map_pow]
    apply isIdempotentElem_one_sub_one_sub_pow_pow
    -- `(x - x²)^n ∈ I B`
    obtain ⟨g, hg⟩ := Matrix.charpoly_dvd_X_sub_X_sq_pow_of_isIdempotentElem hM
    obtain ⟨G, rfl⟩ := Polynomial.map_surjective _ Ideal.Quotient.mk_surjective g
    rw [Fintype.card_fin, ← hX₀, Matrix.charpoly_map] at hg
    have hmem : (X - X ^ 2) ^ n - f * G ∈ I.map (C : A →+* A[X]) := by
      rw [← Ideal.mk_ker (I := I), ← Polynomial.ker_mapRingHom, RingHom.mem_ker,
        Polynomial.coe_mapRingHom, Polynomial.map_sub, sub_eq_zero, Polynomial.map_mul]
      simpa [f] using hg
    have hmem' : (x - x ^ 2) ^ n ∈ I.map (algebraMap A (AdjoinRoot f)) := by
      have := Ideal.mem_map_of_mem (aeval x).toRingHom hmem
      rw [Ideal.map_map] at this
      have hc : (aeval x).toRingHom.comp C = algebraMap A (AdjoinRoot f) := by
        ext; simp
      rw [hc] at this
      have hfx : aeval x f = 0 := by simp [x, AdjoinRoot.aeval_eq]
      simpa [hfx] using this
    have h0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem'
    rw [pow_succ]
    simp only [map_pow, map_sub] at h0 ⊢
    rw [h0, zero_mul]
  · have h1 : (ψ (1 - (1 - x ^ N) ^ N)).map (Ideal.Quotient.mk I) =
        (RingHom.mapMatrix (Ideal.Quotient.mk I)) (ψ (1 - (1 - x ^ N) ^ N)) := rfl
    have h2 : (RingHom.mapMatrix (Ideal.Quotient.mk I)) X₀ = M := hX₀
    rw [h1, map_sub, map_one, map_pow, map_sub, map_one, map_pow, map_sub, map_one, map_pow,
      map_sub, map_one, map_pow, hψx, h2, hM.pow_succ_eq, hM.one_sub.pow_succ_eq, sub_sub_cancel]
