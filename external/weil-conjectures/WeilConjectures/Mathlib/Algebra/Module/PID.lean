/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Module.PID
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-!
# Finitely generated modules over a discrete valuation ring

A finitely generated module over a discrete valuation ring is the product of a finite free
module and a module killed by a power of the uniformizer.
-/

@[expose] public section

universe u v

open DirectSum

namespace Module

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Over a discrete valuation ring, a finite direct sum of quotients by powers of
irreducible elements is killed by a power of any uniformizer. -/
theorem pow_smul_eq_zero_of_directSum {ϖ : R} (hϖ : Irreducible ϖ)
    {ι : Type u} [Finite ι] (p : ι → R) (hp : ∀ i, Irreducible (p i)) (e : ι → ℕ) :
    ∃ k : ℕ, ∀ x : ⨁ i : ι, R ⧸ R ∙ p i ^ e i, ϖ ^ k • x = 0 := by
  classical
  cases nonempty_fintype ι
  refine ⟨∑ i, e i, fun x ↦ ?_⟩
  ext i
  rw [DirectSum.smul_apply, DirectSum.zero_apply]
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x i)
  rw [← ha, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
  change ϖ ^ (∑ j, e j) * a ∈ Ideal.span {p i ^ e i}
  rw [Ideal.mem_span_singleton]
  obtain ⟨u, hu⟩ := IsDiscreteValuationRing.associated_of_irreducible R (hp i) hϖ
  have hle : e i ≤ ∑ j, e j :=
    Finset.single_le_sum (f := e) (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
  refine Dvd.dvd.mul_right ?_ a
  rw [← hu, ← pow_mul_pow_sub (p i * u) hle, mul_pow]
  exact Dvd.dvd.mul_right (dvd_mul_right _ _) _

/-- A finitely generated module over a discrete valuation ring is the product of a finite
free module and a module killed by a power of the uniformizer. -/
theorem exists_equiv_free_prod_pow_smul_eq_zero {ϖ : R} (hϖ : Irreducible ϖ)
    (M : Type v) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (n : ℕ) (N : Type u) (_ : AddCommGroup N) (_ : Module R N) (k : ℕ),
      Nonempty (M ≃ₗ[R] (Fin n →₀ R) × N) ∧ ∀ x : N, ϖ ^ k • x = 0 := by
  obtain ⟨n, ι, _, p, hp, e, ⟨f⟩⟩ := Module.equiv_free_prod_directSum R M
  obtain ⟨k, hk⟩ := pow_smul_eq_zero_of_directSum hϖ p hp e
  exact ⟨n, _, inferInstance, inferInstance, k, ⟨f⟩, hk⟩

end Module
