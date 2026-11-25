/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdjoinRoot

import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Ideal.GoingUp
import WeilConjectures.Mathlib.RingTheory.DiscreteValuationRing.TFAE

/-! # The DVR obtained by adjoining a root of a uniformizer

## References

* Stacks Project, Tags 09EV and 00PD
* Stacks Project, Tag 09EV (and evaluation for n = 1)
-/

@[expose] public section
universe u
namespace AlgebraicGeometry.Scheme

/-- Adjoining a positive-order root of a DVR uniformizer gives a DVR with that root
as uniformizer. -/
theorem dvr_uniformizer_root_algebra
    (B : Type u) [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
    (pi : B) (hpi : Irreducible pi) (n : ℕ) (hn : 0 < n) :
    let A := AdjoinRoot ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)
    ∃ (_ : IsDomain A) (_ : IsDiscreteValuationRing A),
      IsLocalRing.maximalIdeal A = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial B) ^ n - Polynomial.C pi)} := by
  classical
  let f := (Polynomial.X : Polynomial B) ^ n - Polynomial.C pi
  let A := AdjoinRoot f
  let t : A := AdjoinRoot.root f
  have hf : f.Monic := Polynomial.monic_X_pow_sub_C pi hn.ne'
  have hdeg : f.natDegree = n := Polynomial.natDegree_X_pow_sub_C
  have hei : f.IsEisensteinAt (Ideal.span {pi}) := by
    apply hf.isEisensteinAt_of_mem_of_notMem
    · rw [← hpi.maximalIdeal_eq]
      exact (IsLocalRing.maximalIdeal.isMaximal B).ne_top
    · intro i hi
      rw [hdeg] at hi
      by_cases hi0 : i = 0
      · subst i
        simp [f, Ne.symm hn.ne', Polynomial.coeff_X_pow]
      · simp [f, Polynomial.coeff_X_pow, ne_of_lt hi, Polynomial.coeff_C, hi0]
    · simp only [f, Polynomial.coeff_sub, Polynomial.coeff_X_pow,
        Ne.symm hn.ne', ite_false, Polynomial.coeff_C_zero, zero_sub,
        Ideal.neg_mem_iff, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      rintro ⟨b, hb⟩
      have hb' : 1 = pi * b := mul_left_cancel₀ hpi.ne_zero (by
        calc pi * 1 = pi := mul_one pi
             _ = pi ^ 2 * b := hb
             _ = pi * (pi * b) := by ring)
      exact hpi.not_isUnit (isUnit_of_dvd_one ⟨b, hb'⟩)
  have hirr : Irreducible f := hei.irreducible
    (by rw [← hpi.maximalIdeal_eq]; infer_instance) hf.isPrimitive (hdeg ▸ hn)
  let hdom : IsDomain A := AdjoinRoot.isDomain_of_prime hirr.prime
  let := hf.finite_adjoinRoot
  have hrel : t ^ n = algebraMap B A pi := by
    simpa only [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using
      (AdjoinRoot.eval₂_root f)
  let k := B ⧸ Ideal.span {pi}
  let : (Ideal.span {pi}).IsMaximal := by rw [← hpi.maximalIdeal_eq]; infer_instance
  let : Field k := Ideal.Quotient.field _
  let φ : A →+* k := AdjoinRoot.lift (f := f) (Ideal.Quotient.mk _) 0 (by
    simp only [f, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, zero_pow hn.ne', zero_sub, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self pi))
  have hφ : Function.Surjective φ := by
    intro b
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
    refine ⟨AdjoinRoot.of f b, ?_⟩
    exact AdjoinRoot.lift_of _
  let J : Ideal A := Ideal.span {t}
  let θ : A →+* A ⧸ J := Ideal.Quotient.mk J
  have ht : θ t = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
    (Ideal.mem_span_singleton_self t)
  have hpi0 : θ (algebraMap B A pi) = 0 := by rw [← hrel, map_pow, ht, zero_pow hn.ne']
  let ψ : k →+* A ⧸ J := Ideal.Quotient.lift (Ideal.span {pi})
    (θ.comp (algebraMap B A)) (by
      intro b hb
      obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hb
      simp [hpi0])
  have hcomp : ψ.comp φ = θ := by
    apply AdjoinRoot.ringHom_ext
    · ext b
      change ψ (φ (AdjoinRoot.of f b)) = θ (AdjoinRoot.of f b)
      rw [show φ (AdjoinRoot.of f b) = Ideal.Quotient.mk (Ideal.span {pi}) b
        from AdjoinRoot.lift_of _]
      exact Ideal.Quotient.lift_mk _ _ _
    · change ψ (φ t) = θ t
      rw [show φ t = 0 from AdjoinRoot.lift_root _, map_zero, ht]
  have hker : RingHom.ker φ = J := by
    apply le_antisymm
    · intro b hb
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      change θ b = 0
      rw [← hcomp]
      simp only [RingHom.comp_apply, RingHom.mem_ker.mp hb, map_zero]
    · apply Ideal.span_le.mpr
      intro b hb
      obtain rfl := Set.mem_singleton_iff.mp hb
      change φ t = 0
      exact AdjoinRoot.lift_root _
  have hJ : J.IsMaximal := hker ▸ RingHom.ker_isMaximal_of_surjective φ hφ
  have huniq : ∀ M : Ideal A, M.IsMaximal → M = J := by
    intro M hM
    let := hM
    have hc : M.comap (algebraMap B A) = IsLocalRing.maximalIdeal B :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal M)
    have hpiM : algebraMap B A pi ∈ M := by
      change pi ∈ M.comap (algebraMap B A)
      rw [hc, hpi.maximalIdeal_eq]
      exact Ideal.mem_span_singleton_self pi
    have htM : t ∈ M := hM.isPrime.mem_of_pow_mem n (hrel ▸ hpiM)
    exact (hJ.eq_of_le hM.ne_top
      (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr htM))).symm
  let : IsLocalRing A := IsLocalRing.of_unique_max_ideal ⟨J, hJ, huniq⟩
  have hmax : IsLocalRing.maximalIdeal A = J := (IsLocalRing.eq_maximalIdeal hJ).symm
  have htne : t ≠ 0 := by
    intro ht0
    have hpiA : algebraMap B A pi = 0 := by rw [← hrel, ht0, zero_pow hn.ne']
    have hinj : Function.Injective (algebraMap B A) := by
      apply AdjoinRoot.of.injective_of_degree_ne_zero
      rw [Polynomial.degree_eq_natDegree hf.ne_zero, hdeg]
      exact_mod_cast hn.ne'
    exact hpi.ne_zero (hinj (hpiA.trans (map_zero _).symm))
  exact ⟨hdom, IsDiscreteValuationRing.of_maximalIdeal_eq_span_singleton htne hmax, hmax⟩

end AlgebraicGeometry.Scheme
