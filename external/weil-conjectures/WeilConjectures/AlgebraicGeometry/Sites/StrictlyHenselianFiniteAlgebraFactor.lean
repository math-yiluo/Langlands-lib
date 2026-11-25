/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.RingTheory.FiniteOverHenselianLocalProduct
public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.PurelyInseparable.Basic

/-!
# Local factors of finite algebras over strictly henselian local rings

Let `A` be a strictly henselian local ring and `B` a finite `A`-algebra. Then `B` is a finite
product of local rings (Stacks, Tag 04GH), each finite over `A`, hence henselian with residue
field finite over the separably closed residue field of `A`, hence strictly henselian. So for
every prime `q` of `B` there is an idempotent `e` of `B` with `e ∉ q` such that
`B ⧸ (1 - e) ≅ B[1/e]` is a strictly henselian local ring: the local factor of `B` through `q`.

## References

- Stacks Project, Lemma 10.153.4, <https://stacks.math.columbia.edu/tag/04GH>
- Stacks Project, Lemma 10.153.10 and 10.155.4 (finite algebras over (strictly) henselian rings)
-/

@[expose] public section

universe u v

namespace IsStrictlyHenselianLocalRing

/-- **The local factor through a prime.** Let `A` be a strictly henselian local ring and `B` a
finite `A`-algebra. For every prime `q` of `B` there is an idempotent `e` of `B` with
`1 - e ∈ q` such that `B ⧸ (1 - e)` is a strictly henselian local ring. -/
theorem exists_isIdempotentElem_quotient (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [IsStrictlyHenselianLocalRing A] [Algebra A B] [Module.Finite A B] (q : Ideal B)
    [q.IsPrime] :
    ∃ e : B, IsIdempotentElem e ∧ 1 - e ∈ q ∧
      IsStrictlyHenselianLocalRing (B ⧸ Ideal.span {1 - e}) := by
  classical
  obtain ⟨r, C, rings, algs, hens, locs, ⟨φ⟩, -, hres⟩ :=
    HenselianLocalRing.finite_over_henselian_exists_algEquiv_pi A B
  let e (i : Fin r) : B := φ.symm (Pi.single i 1)
  have he (i : Fin r) : IsIdempotentElem (e i) := by
    rw [IsIdempotentElem, ← map_mul, ← Pi.single_mul, mul_one]
  have hsum : ∑ i, e i = 1 := by
    have h1 : ∑ i, (Pi.single i 1 : ∀ j, C j) = 1 := Finset.univ_sum_single (1 : ∀ i, C i)
    rw [← map_sum, h1, map_one]
  obtain ⟨i, hi⟩ : ∃ i, e i ∉ q := by
    by_contra! h
    exact Ideal.IsPrime.ne_top ‹_› ((Ideal.eq_top_iff_one q).2
      (hsum ▸ Ideal.sum_mem q fun i _ ↦ h i))
  refine ⟨e i, he i, ?_, ?_⟩
  · refine (Ideal.IsPrime.mem_or_mem ‹_› ?_).resolve_left hi
    rw [mul_sub, mul_one, (he i).eq, sub_self]
    exact q.zero_mem
  · let π : B →+* C i := (Pi.evalRingHom C i).comp φ.toRingEquiv.toRingHom
    have hπ : Function.Surjective π := fun c ↦ ⟨φ.symm (Pi.single i c), by simp [π]⟩
    have hker : RingHom.ker π = Ideal.span {1 - e i} := by
      apply le_antisymm
      · intro x hx
        rw [RingHom.mem_ker] at hx
        have h0 : e i * x = 0 := by
          apply φ.injective
          rw [map_mul, map_zero, AlgEquiv.apply_symm_apply]
          funext j
          rw [Pi.mul_apply, Pi.zero_apply]
          by_cases hj : j = i
          · subst hj
            exact (mul_eq_zero_of_right _ hx)
          · rw [Pi.single_eq_of_ne hj, zero_mul]
        rw [Ideal.mem_span_singleton']
        exact ⟨x, by rw [mul_sub, mul_one, mul_comm, h0, sub_zero]⟩
      · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker,
          map_sub, map_one]
        simp [π, e]
    let ψ : B ⧸ Ideal.span {1 - e i} ≃+* C i :=
      (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hπ)
    have : Algebra.IsAlgebraic (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField (C i)) :=
      have := hres i
      Algebra.IsAlgebraic.of_finite _ _
    have : IsSepClosed (IsLocalRing.ResidueField (C i)) :=
      Algebra.IsAlgebraic.isSepClosed (F := IsLocalRing.ResidueField A)
    have : IsStrictlyHenselianLocalRing (C i) := ⟨this⟩
    exact IsStrictlyHenselianLocalRing.of_ringEquiv ψ.symm

end IsStrictlyHenselianLocalRing
