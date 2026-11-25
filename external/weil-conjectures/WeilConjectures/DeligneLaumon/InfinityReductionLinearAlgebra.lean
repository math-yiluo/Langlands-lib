/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Eigenvalue bounds and positive powers

The linear algebra in the first step of infinity reduction does not need semisimplicity.
-/

@[expose] public section
set_option autoImplicit false
universe u v w
open Polynomial

namespace WeilConjectures

private theorem injective_aeval_prod
    {R : Type u} [CommRing R] {V : Type v} [AddCommGroup V] [Module R V]
    (f : Module.End R V) (L : List R)
    (h : ∀ a ∈ L, ¬ f.HasEigenvalue a) :
    Function.Injective (aeval f ((L.map (fun a ↦ X - C a)).prod)) := by
  induction L with
  | nil =>
      intro x y hxy
      simpa using hxy
  | cons a L ih =>
    have ha : Function.Injective (f - a • (1 : Module.End R V)) := by
      rw [← LinearMap.ker_eq_bot, ← Module.End.eigenspace_def]
      exact not_ne_iff.mp (h a (by simp))
    have hL := ih (fun b hb ↦ h b (by simp [hb]))
    simp only [List.map_cons, List.prod_cons, map_mul, map_sub, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one]
    intro x y hxy
    exact hL (ha hxy)

/-- Every eigenvalue of a positive power is a power of an eigenvalue. Scalars can be any
quotient of an algebraically closed field, and the module need not be finite dimensional.
Source: latest blueprint, infinity-reduction proof, eigenvalue power comparison
(blueprint: lem-wft-infinity-eigenvalue-powers).

Proof: lift the eigenvalue to the algebraically closed field and factor X^m minus that lift
into its monic linear factors. If no root gave an eigenvalue of the original operator, each
linear factor evaluated at the operator would be injective. Their product would be injective,
contradicting the nonzero eigenvector of the power. Evaluation at the chosen root gives the
claimed scalar power identity. This also covers the zero module and zero eigenvalues. -/
theorem infinity_eigenvalue_power_preimage
    {K : Type u} [Field K] [IsAlgClosed K]
    {R : Type v} [CommRing R] (s : K →+* R) (hs : Function.Surjective s)
    {V : Type w} [AddCommGroup V] [Module R V]
    (f : Module.End R V) (m : ℕ) (hm : 0 < m) (β : R)
    (hβ : (f ^ m).HasEigenvalue β) :
    ∃ α : R, f.HasEigenvalue α ∧ α ^ m = β := by
  classical
  obtain ⟨b, rfl⟩ := hs β
  let p : K[X] := X ^ m - C b
  have hp : p.Monic := monic_X_pow_sub_C b (Nat.ne_zero_of_lt hm)
  have hfac := (IsAlgClosed.splits p).eq_prod_roots_of_monic hp
  by_contra hn
  have hn' : ∀ a ∈ p.roots.toList, ¬ f.HasEigenvalue (s a) := by
    intro a ha he
    apply hn
    have ha' : p.IsRoot a := (mem_roots hp.ne_zero).mp (by simpa using ha)
    have hab : a ^ m = b := by simpa [p, IsRoot, sub_eq_zero] using ha'
    exact ⟨s a, he, by rw [← map_pow, hab]⟩
  have hinj := injective_aeval_prod f (p.roots.toList.map s) (by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp ha
    exact hn' b hb)
  have heq : ((p.roots.toList.map s).map (fun a ↦ (X - C a : R[X]))).prod = p.map s := by
    conv_rhs => rw [hfac, ← Multiset.prod_toList, Polynomial.map_list_prod]
    simp [List.map_map, Polynomial.map_sub]
  rw [heq] at hinj
  obtain ⟨x, hx⟩ := hβ.exists_hasEigenvector
  have hz : aeval f (p.map s) x = 0 := by
    simpa [p, sub_eq_zero, Algebra.algebraMap_eq_smul_one] using
      sub_eq_zero.mpr hx.apply_eq_smul
  exact hx.2 (hinj (hz.trans (map_zero _).symm))

/-- An intertwining linear equivalence preserves every eigenvalue.
Source: latest blueprint, infinity-reduction proof, identification of geometric cohomology
(blueprint: lem-wft-infinity-eigenvalue-powers).

Proof: send a nonzero eigenvector through the equivalence; linearity preserves its
scalar equation and injectivity preserves nonzeroness. Apply the same argument to
the inverse equivalence for the reverse implication. -/
theorem infinity_eigenvalue_equiv
    {R : Type u} [CommRing R]
    {V : Type v} [AddCommGroup V] [Module R V]
    {W : Type w} [AddCommGroup W] [Module R W]
    (f : Module.End R V) (g : Module.End R W) (e : V ≃ₗ[R] W)
    (h : ∀ x, e (f x) = g (e x)) (α : R) :
    f.HasEigenvalue α ↔ g.HasEigenvalue α := by
  constructor
  · intro hα
    obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := e x)
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff, ← h, hx.apply_eq_smul, e.map_smul]
    · intro hz
      exact hx.2 (e.injective (hz.trans e.map_zero.symm))
  · intro hα
    obtain ⟨x, hx⟩ := hα.exists_hasEigenvector
    apply Module.End.hasEigenvalue_of_hasEigenvector (x := e.symm x)
    refine ⟨?_, ?_⟩
    · rw [Module.End.mem_eigenspace_iff]
      apply e.injective
      rw [h, e.apply_symm_apply, e.map_smul, e.apply_symm_apply, hx.apply_eq_smul]
    · intro hz
      apply hx.2
      have he := congrArg e hz
      simpa using he

/-- A positive power preserves the normalized eigenvalue bound when the cardinality is
raised to the same power.
Source: latest blueprint, infinity-reduction proof, first assertion
(blueprint: lem-wft-infinity-eigenvalue-powers).

Proof: every eigenvalue of the operator yields its m-th power for the powered operator,
and the preceding factorization argument gives the converse. The norm of a power is the
power of the norm. The nonnegative real power identity converts the cardinality bound,
and the positive integer power is order-reflecting on nonnegative reals. -/
theorem infinity_eigenvalue_bound_power_iff
    {K : Type u} [Field K] [IsAlgClosed K]
    {R : Type v} [CommRing R] (s : K →+* R) (hs : Function.Surjective s)
    {V : Type w} [AddCommGroup V] [Module R V]
    (f : Module.End R V) (ι : R →+* ℂ) (q m : ℕ) (hm : 0 < m) (b : ℝ) :
    (∀ α : R, f.HasEigenvalue α → ‖ι α‖ ≤ (q : ℝ) ^ (b / 2)) ↔
      (∀ β : R, (f ^ m).HasEigenvalue β → ‖ι β‖ ≤ ((q ^ m : ℕ) : ℝ) ^ (b / 2)) := by
  have hp : ((q ^ m : ℕ) : ℝ) ^ (b / 2) = ((q : ℝ) ^ (b / 2)) ^ m := by
    rw [Nat.cast_pow, ← Real.rpow_natCast ((q : ℝ) ^ (b / 2)) m,
      ← Real.rpow_mul (Nat.cast_nonneg _), ← Real.rpow_natCast (q : ℝ) m,
      ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
  constructor
  · intro h β hβ
    obtain ⟨α, hα, rfl⟩ := infinity_eigenvalue_power_preimage s hs f m hm β hβ
    rw [map_pow, norm_pow, hp]
    exact pow_le_pow_left₀ (norm_nonneg _) (h α hα) m
  · intro h α hα
    have hb := h (α ^ m) (hα.pow m)
    rw [map_pow, norm_pow, hp] at hb
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
      (Nat.ne_zero_of_lt hm)).mp hb

end WeilConjectures
