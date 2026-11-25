/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.Unramified.Finite
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.RatFunc.AsPolynomial
public import WeilConjectures.Mathlib.RingTheory.NoetherNormalization
public import WeilConjectures.RingTheory.ConstantField

/-!
# Commutative algebra for the affine Artin vanishing theorem

* `ringKrullDim_le_of_trdeg_le`: a finitely generated algebra over a field has Krull dimension
  at most its transcendence degree.
-/

@[expose] public section

open Polynomial

universe u v

/-- A finitely generated algebra `A` over a field `k` has Krull dimension at most its
transcendence degree: by Noether normalization `A` is finite over a polynomial subalgebra
`k[X₁, …, Xₛ]`, whose variables are algebraically independent in `A`, and `dim A = s`. -/
theorem ringKrullDim_le_of_trdeg_le (k : Type u) (A : Type v) [Field k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] {n : ℕ} (h : Algebra.trdeg k A ≤ n) :
    ringKrullDim A ≤ n := by
  cases subsingleton_or_nontrivial A with
  | inl hA => simp [ringKrullDim_eq_bot_of_subsingleton]
  | inr hA =>
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  rw [ringKrullDim_eq_of_finite_inj_algHom_mvPolynomial g hinj hfin]
  have hind : AlgebraicIndependent k (g ∘ MvPolynomial.X) :=
    (MvPolynomial.algebraicIndependent_X (Fin s) k).map' hinj
  have := hind.lift_cardinalMk_le_trdeg.trans (Cardinal.lift_le.2 h)
  simp only [Cardinal.mk_fin, Cardinal.lift_natCast, Nat.cast_le] at this
  exact_mod_cast this

section Henselian

variable (k : Type u) (R : Type v) [Field k] [CommRing R] [IsDomain R] [Algebra k R]

/-- Let `R` be a henselian local domain with separably closed residue field, containing a field
`k`. Then `R` contains a separably closed field `F ⊇ k`, namely the integral closure of `k` in
`R`: a separable irreducible polynomial over it has a simple root in the residue field, which
lifts by Hensel's lemma to a root in `R`, integral over `k`. -/
theorem exists_isSepClosed_of_henselianLocalRing [HenselianLocalRing R]
    [IsSepClosed (IsLocalRing.ResidueField R)] :
    ∃ (F : Type v) (_ : Field F) (_ : IsSepClosed F) (_ : Algebra k F) (_ : Algebra F R),
      IsScalarTower k F R := by
  let F := integralClosure k R
  let : Field F := (Algebra.TensorProduct.isField_integralClosure (k := k) (A := R)).toField
  refine ⟨F, inferInstance, ?_, inferInstance, inferInstance, inferInstance⟩
  refine IsSepClosed.of_exists_root _ fun p hmon hirr hsep ↦ ?_
  let ι : F →+* R := algebraMap F R
  let π : F →+* IsLocalRing.ResidueField R := (IsLocalRing.residue R).comp ι
  have hdeg : (p.map π).degree ≠ 0 := by
    rw [degree_map]
    exact fun h ↦ hirr.not_isUnit (isUnit_iff_degree_eq_zero.2 h)
  obtain ⟨a₀, ha₀⟩ := IsSepClosed.exists_root (p.map π) hdeg (hsep.map)
  obtain ⟨r₀, rfl⟩ := IsLocalRing.residue_surjective a₀
  have hmapR : (p.map ι).map (IsLocalRing.residue R) = p.map π := by
    rw [Polynomial.map_map]
  obtain ⟨r, hr, -⟩ := HenselianLocalRing.is_henselian (p.map ι) (hmon.map ι) r₀
    (by
      rw [← IsLocalRing.residue_eq_zero_iff, ← Polynomial.eval_map_apply, hmapR]
      exact ha₀)
    (by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, ← Polynomial.eval_map_apply,
        ← Polynomial.derivative_map, hmapR, Polynomial.derivative_map, Polynomial.eval_map]
      refine hsep.eval₂_derivative_ne_zero π ?_
      rwa [← Polynomial.eval_map])
  have hint : IsIntegral k r := by
    have h₁ : IsIntegral F r := ⟨p, hmon, by rwa [Polynomial.IsRoot, Polynomial.eval_map] at hr⟩
    exact isIntegral_trans (R := k) (A := F) r h₁
  refine ⟨(⟨r, hint⟩ : integralClosure k R), ι.injective ?_⟩
  rw [map_zero, ← Polynomial.eval₂_hom, ← Polynomial.eval_map]
  exact hr

end Henselian

section RatFunc

variable {F : Type u} {R : Type v} [Field F] [CommRing R] [IsLocalRing R] [Algebra F R]

/-- In a local ring `R` containing a field `F`, a polynomial over `F` with nonzero constant term
evaluates at an element `u` of the maximal ideal to a unit. -/
theorem isUnit_aeval_of_coeff_zero_ne_zero {u : R} (hu : u ∈ IsLocalRing.maximalIdeal R)
    {q : F[X]} (hq : q.coeff 0 ≠ 0) : IsUnit (aeval u q) := by
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit, aeval_def, hom_eval₂,
    (IsLocalRing.residue_eq_zero_iff u).2 hu, eval₂_at_zero, RingHom.comp_apply]
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2
    ((Ne.isUnit hq).map (algebraMap F R))

/-- Let `R` be a local ring containing a field `F`, `u` an element of the maximal ideal of `R`,
and `S = R[1/u]`. Then `x ↦ u` extends to a ring homomorphism `F(x) ⟶ S`: a nonzero polynomial
`p` over `F` is `xᵏ q` with `q(0) ≠ 0`, so that `p(u) = uᵏ q(u)` is a unit in `S`. -/
theorem exists_ratFunc_ringHom_of_mem_maximalIdeal {u : R}
    (hu : u ∈ IsLocalRing.maximalIdeal R) (S : Type*) [CommRing S] [Algebra R S]
    [IsLocalization.Away u S] :
    ∃ φ : RatFunc F →+* S, φ (RatFunc.X) = algebraMap R S u ∧
      ∀ c : F, φ (RatFunc.C c) = algebraMap R S (algebraMap F R c) := by
  let ψ : F[X] →+* S := (algebraMap R S).comp (aeval u).toRingHom
  have hψ (p : nonZeroDivisors F[X]) : IsUnit (ψ p) := by
    have hp : (p : F[X]) ≠ 0 := nonZeroDivisors.coe_ne_zero p
    obtain ⟨q, hq⟩ : X ^ (p : F[X]).natTrailingDegree ∣ (p : F[X]) :=
      X_pow_dvd_iff.2 fun d hd ↦ coeff_eq_zero_of_lt_natTrailingDegree hd
    have hq0 : q.coeff 0 ≠ 0 := by
      have := congrArg (fun r : F[X] ↦ r.coeff (p : F[X]).natTrailingDegree) hq
      simp only [coeff_X_pow_mul', le_refl, ↓reduceIte, Nat.sub_self] at this
      rw [← this]
      exact mt trailingCoeff_eq_zero.1 hp
    simp only [ψ, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [hq, map_mul, map_mul, map_pow, map_pow, aeval_X]
    exact ((IsLocalization.Away.algebraMap_isUnit u).pow _).mul
      ((isUnit_aeval_of_coeff_zero_ne_zero hu hq0).map _)
  refine ⟨IsLocalization.lift (M := nonZeroDivisors F[X]) hψ, ?_, fun c ↦ ?_⟩
  · rw [← RatFunc.algebraMap_X, IsLocalization.lift_eq]
    simp [ψ]
  · rw [← RatFunc.algebraMap_C, IsLocalization.lift_eq]
    simp [ψ]

end RatFunc

section Etale

open TensorProduct

/-- An étale algebra `B` over a domain `P` is algebraic: after base change to the fraction field
`K` of `P` it becomes an étale, hence finite, `K`-algebra, so every element of `B` satisfies a
nonzero polynomial over `K` after inverting a nonzero element of `P`. -/
theorem Algebra.IsAlgebraic.of_etale (P : Type u) (B : Type v) [CommRing P] [IsDomain P]
    [CommRing B] [Algebra P B] [Algebra.Etale P B] : Algebra.IsAlgebraic P B := by
  let K := FractionRing P
  have : Module.Finite K (K ⊗[P] B) := Algebra.FormallyUnramified.finite_of_free K _
  refine ⟨fun b ↦ ?_⟩
  have h₁ : IsAlgebraic K ((1 : K) ⊗ₜ[P] b) :=
    (Algebra.IsIntegral.isIntegral (R := K) _).isAlgebraic
  obtain ⟨p, hp, hpb⟩ := (IsFractionRing.isAlgebraic_iff P K (K ⊗[P] B)).2 h₁
  have h₂ : TensorProduct.mk P K B 1 (aeval b p) = TensorProduct.mk P K B 1 0 := by
    rw [TensorProduct.mk_apply, TensorProduct.mk_apply, tmul_zero, ← hpb,
      ← Algebra.TensorProduct.includeRight_apply, ← Polynomial.aeval_algHom_apply]
    rfl
  have hloc : IsLocalizedModule (nonZeroDivisors P) (TensorProduct.mk P K B 1) :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors P) K _).2
      (TensorProduct.isBaseChange P B K)
  obtain ⟨c, hc⟩ := hloc.exists_of_eq h₂
  refine ⟨(c : P) • p, smul_ne_zero (nonZeroDivisors.coe_ne_zero c) hp, ?_⟩
  rw [smul_zero] at hc
  rw [map_smul]
  exact hc

end Etale
