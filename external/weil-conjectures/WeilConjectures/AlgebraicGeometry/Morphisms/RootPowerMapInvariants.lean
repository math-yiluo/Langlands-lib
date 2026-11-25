/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RootsOfUnity.Basic
public import Mathlib.GroupTheory.Index

/-! # Image of the intermediate power map in a root algebra

## References

* Stacks Project, Tags 0EYG and 09EV, intermediate-root calculation, expanded as a monic-basis
  calculation without a domain hypothesis
* Stacks Project, Tag 0EYG, final intermediate-field paragraph, and Tag 09EV, cyclic
  intermediate-root calculation
-/

@[expose] public section

universe u
set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- Let `K` be a subgroup of the `n`-th roots of unity, acting on `H[X] ⧸ (X ^ n - h)` via `ρ`.
The intermediate power map `φ : H[X] ⧸ (X ^ [μ_n : K] - h) → H[X] ⧸ (X ^ n - h)` sending the
root to the `#K`-th power of the root is injective, with image the `K`-invariant elements. -/
theorem root_power_map_invariants
    (H : Type u) [CommRing H] (h : H) (n : ℕ) (hn : 0 < n)
    [Finite (rootsOfUnity n H)] [IsCyclic (rootsOfUnity n H)]
    (hcard : Nat.card (rootsOfUnity n H) = n)
    (hsep : ∀ ζ : rootsOfUnity n H, ζ ≠ 1 → IsUnit (((ζ : Hˣ) : H) - 1))
    (K : Subgroup (rootsOfUnity n H))
    (ρ : rootsOfUnity n H →
      (AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) →ₐ[H]
        AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)))
    (hρ : ∀ ζ, ρ ζ (AdjoinRoot.root
      ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)) =
        algebraMap H _ ((ζ : Hˣ) : H) * AdjoinRoot.root _)
    (φ : AdjoinRoot ((Polynomial.X : Polynomial H) ^ K.index - Polynomial.C h) →ₐ[H]
      AdjoinRoot ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h))
    (hφ : φ (AdjoinRoot.root _) =
      AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h) ^ Nat.card K) :
    Function.Injective φ ∧ ∀ x, (∀ ζ : K, ρ ζ.val x = x) ↔ x ∈ Set.range φ := by
  have hinj : Function.Injective φ := by
    nontriviality H using
      (by
        haveI : Subsingleton (AdjoinRoot
          ((Polynomial.X : Polynomial H) ^ K.index - Polynomial.C h)) :=
            Module.subsingleton H _
        exact Function.injective_of_subsingleton φ)
    have he : 0 < K.index := Nat.pos_of_ne_zero K.index_ne_zero_of_finite
    have hr : 0 < Nat.card K := Nat.card_pos
    have hre : Nat.card K * K.index = n := K.card_mul_index.trans hcard
    let bn := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C h hn.ne')
    let be := AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C h he.ne')
    have dn : bn.dim = n := Polynomial.natDegree_X_pow_sub_C
    have de : be.dim = K.index := Polynomial.natDegree_X_pow_sub_C
    let f : Fin be.dim → Fin bn.dim := fun i ↦
      ⟨Nat.card K * i.val, by
        exact (Nat.mul_lt_mul_of_pos_left (i.isLt.trans_eq de) hr).trans_eq
          (hre.trans dn.symm)⟩
    have hf : Function.Injective f := by
      intro i j hij
      apply Fin.ext
      exact Nat.eq_of_mul_eq_mul_left hr (congrArg Fin.val hij)
    apply LinearMap.injective_of_linearIndependent (f := φ.toLinearMap) be.basis.span_eq
    convert bn.basis.linearIndependent.comp f hf using 1
    funext i
    simp only [Function.comp_apply, AlgHom.toLinearMap_apply, be.basis_eq_pow,
      bn.basis_eq_pow, map_pow]
    rw [show be.gen = AdjoinRoot.root _ from rfl, hφ, ← pow_mul]
    rfl
  refine ⟨hinj, ?_⟩
  classical
  rcases subsingleton_or_nontrivial H with hH | hH
  · have := hH
    have : Subsingleton (AdjoinRoot
      ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h)) := Module.subsingleton H _
    intro x
    constructor
    · intro _
      exact ⟨0, Subsingleton.elim _ _⟩
    · intro _ ζ
      exact Subsingleton.elim _ _
  have := hH
  let b := (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C h hn.ne')).basis
  have hb (i : Fin ((Polynomial.X : Polynomial H) ^ n - Polynomial.C h).natDegree) :
      b i = AdjoinRoot.root _ ^ i.val :=
    (AdjoinRoot.powerBasis' (Polynomial.monic_X_pow_sub_C h hn.ne')).basis_eq_pow i
  have haction (ζ : rootsOfUnity n H) (i) :
      ρ ζ (b i) = (((ζ : Hˣ) : H) ^ i.val) • b i := by
    rw [hb, map_pow, hρ, mul_pow, Algebra.smul_def, map_pow]
  have hcoeff (ζ : rootsOfUnity n H) (x) (i) :
      b.repr (ρ ζ x) i = (((ζ : Hˣ) : H) ^ i.val) * b.repr x i := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, haction, smul_smul, Finsupp.coe_finsetSum,
      Finset.sum_apply, Finsupp.coe_smul, Pi.smul_apply,
      b.repr_self_apply, smul_eq_mul]
    simp [mul_comm]
  obtain ⟨z, hz⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := K)
  have hzero (x) (hx : ∀ ζ : K, ρ ζ.val x = x) (i)
      (hi : ¬ Nat.card K ∣ i.val) : b.repr x i = 0 := by
    have hzpow : z.val ^ i.val ≠ 1 := by
      intro hp
      have : z ^ i.val = 1 := Subtype.ext hp
      exact hi (hz ▸ orderOf_dvd_of_pow_eq_one this)
    have hu := hsep (z.val ^ i.val) hzpow
    have heq := hcoeff z.val x i
    rw [hx z] at heq
    have hm : ((((z.val : Hˣ) : H) ^ i.val) - 1) * b.repr x i = 0 := by
      rw [sub_mul, one_mul, ← heq, sub_self]
    have hu' : IsUnit ((((z.val : Hˣ) : H) ^ i.val) - 1) := by
      simpa using hu
    exact hu'.mul_left_cancel (by simpa using hm)
  intro x
  constructor
  · intro hx
    refine ⟨∑ i, b.repr x i • (AdjoinRoot.root
      ((Polynomial.X : Polynomial H) ^ K.index - Polynomial.C h)) ^
        (i.val / Nat.card K), ?_⟩
    rw [map_sum]
    calc
      _ = ∑ i, b.repr x i • b i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [map_smul, map_pow, hφ, ← pow_mul]
        by_cases hi : Nat.card K ∣ i.val
        · rw [Nat.mul_div_cancel' hi, hb]
        · rw [hzero x hx i hi, zero_smul, zero_smul]
      _ = x := b.sum_repr x
  · rintro ⟨y, rfl⟩ ζ
    have hzpow : (((ζ.val : Hˣ) : H) ^ Nat.card K) = 1 := by
      have hp : ζ ^ Nat.card K = 1 := pow_card_eq_one'
      have hp' := congrArg (fun w : K ↦ (((w.val : Hˣ) : H))) hp
      simpa only [Subgroup.coe_pow, Subgroup.coe_one, Units.val_pow_eq_pow_val,
        Units.val_one] using hp'
    have heq : (ρ ζ.val).comp φ = φ := by
      apply AdjoinRoot.algHom_ext
      rw [AlgHom.comp_apply, hφ, map_pow, hρ, mul_pow, ← map_pow,
        hzpow, map_one, one_mul]
    exact DFunLike.congr_fun heq y

end AlgebraicGeometry.Scheme
