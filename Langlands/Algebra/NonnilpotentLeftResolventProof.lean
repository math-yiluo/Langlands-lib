import Langlands.Algebra.SeparationStatements
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.LinearAlgebra.Dimension.Basic
import Mathlib.RingTheory.Algebraic.Defs

/-!
# Renard B.III: a nonzero shift without a left inverse

Proof of `Langlands.Renard.NonnilpotentLeftResolventStatement`, the first step of the
proof of Renard's separation lemma B.III (*Représentations des groupes réductifs
p-adiques*, 2026, printed pages 271–273). Suppose every nonzero shift `a - z` has a left
inverse `b z`. If `a` is algebraic, stripping the linear factors of a vanishing polynomial
with these left inverses shows that `a` is nilpotent. If `a` is transcendental, the family
`b` indexed by `ℂ \ {0}` is linearly independent, which is impossible in countable
dimension.
-/

universe u

open Polynomial

namespace Langlands.Renard

/-- If every nonzero shift `a - z` has a left inverse, then a nonzero polynomial `q`
with `a ^ m * q(a) = 0` forces `a` to be nilpotent. Induction on a bound `n` for the
degree of `q`: a root `w` of `q` gives `q = (X - w) q'`; for `w = 0` the factor moves into
the power of `a`, and for `w ≠ 0` it is cancelled by a left inverse of `a - w`. -/
theorem isNilpotent_of_leftInverse_of_aeval_eq_zero {A : Type u} [Ring A] [Algebra ℂ A]
    {a : A} (hleft : ∀ z : ℂ, z ≠ 0 → ∃ b : A, b * (a - algebraMap ℂ A z) = 1) :
    ∀ (n : ℕ) (q : ℂ[X]), q.natDegree ≤ n → q ≠ 0 → ∀ m : ℕ,
      aeval a (X ^ m * q) = 0 → IsNilpotent a := by
  intro n
  induction n with
  | zero =>
    intro q hdeg hq m h
    have hqc : q = C (q.coeff 0) := eq_C_of_natDegree_le_zero hdeg
    have hc : q.coeff 0 ≠ 0 := fun h0 => hq (by rw [hqc, h0, C_0])
    refine ⟨m, ?_⟩
    rw [hqc, map_mul, aeval_X_pow, aeval_C, Algebra.algebraMap_eq_smul_one,
      mul_smul_comm, mul_one] at h
    exact (smul_eq_zero.mp h).resolve_left hc
  | succ n ih =>
    intro q hdeg hq m h
    by_cases hle : q.natDegree ≤ n
    · exact ih q hle hq m h
    have hdeg0 : q.degree ≠ 0 := by
      rw [degree_eq_natDegree hq]
      exact_mod_cast (by omega : q.natDegree ≠ 0)
    obtain ⟨w, hw⟩ := IsAlgClosed.exists_root q hdeg0
    set q' := q /ₘ (X - C w) with hq'def
    have hfac : (X - C w) * q' = q := mul_divByMonic_eq_iff_isRoot.mpr hw
    have hq' : q' ≠ 0 := by
      rintro h0
      rw [h0, mul_zero] at hfac
      exact hq hfac.symm
    have hdeg' : q'.natDegree ≤ n := by
      rw [hq'def, natDegree_divByMonic _ (monic_X_sub_C w), natDegree_X_sub_C]
      omega
    rw [← hfac] at h
    by_cases hw0 : w = 0
    · apply ih q' hdeg' hq' (m + 1)
      rw [← h, hw0, C_0, sub_zero]
      congr 1
      ring
    · obtain ⟨b, hb⟩ := hleft w hw0
      apply ih q' hdeg' hq' m
      have hmul : aeval a (X ^ m * ((X - C w) * q')) =
          (a - algebraMap ℂ A w) * aeval a (X ^ m * q') := by
        rw [show X ^ m * ((X - C w) * q') = (X - C w) * (X ^ m * q') by ring, map_mul,
          map_sub, aeval_X, aeval_C]
      rw [hmul] at h
      calc aeval a (X ^ m * q') = b * (a - algebraMap ℂ A w) * aeval a (X ^ m * q') := by
            rw [hb, one_mul]
        _ = b * ((a - algebraMap ℂ A w) * aeval a (X ^ m * q')) := mul_assoc _ _ _
        _ = 0 := by rw [h, mul_zero]

/-- If `a` is transcendental over `ℂ`, then any family of left inverses `b z` of the
shifts `a - z`, for `z` in a set `s ⊆ ℂ`, is linearly independent. A relation
`∑ g i • b i = 0` over a finite set `t` is multiplied on the right by `N(a)`, where
`N = ∏_{j ∈ t} (X - j)`; this gives `P(a) = 0` for `P = ∑ g i • ∏_{j ∈ t, j ≠ i} (X - j)`.
Transcendence gives `P = 0`, and evaluating `P` at `k ∈ t` gives `g k = 0`. -/
theorem linearIndependent_of_leftInverse_of_transcendental {A : Type u} [Ring A]
    [Algebra ℂ A] {a : A} (ha : Transcendental ℂ a) {s : Set ℂ} (b : s → A)
    (hb : ∀ z : s, b z * (a - algebraMap ℂ A z) = 1) : LinearIndependent ℂ b := by
  classical
  rw [linearIndependent_iff']
  intro t g hg k hk
  set N : ℂ[X] := ∏ j ∈ t, (X - C (j : ℂ)) with hN
  set P : s → ℂ[X] := fun i => ∏ j ∈ t.erase i, (X - C (j : ℂ)) with hP
  have hbN : ∀ i ∈ t, b i * aeval a N = aeval a (P i) := by
    intro i hi
    rw [hN, ← Finset.mul_prod_erase t (fun j : s => X - C (j : ℂ)) hi, map_mul, ← mul_assoc,
      map_sub, aeval_X, aeval_C, hb, one_mul]
  have hsum : aeval a (∑ i ∈ t, g i • P i) = 0 := by
    rw [map_sum]
    calc ∑ i ∈ t, aeval a (g i • P i) = ∑ i ∈ t, g i • (b i * aeval a N) :=
          Finset.sum_congr rfl fun i hi => by rw [map_smul, hbN i hi]
      _ = (∑ i ∈ t, g i • b i) * aeval a N := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun i _ => (smul_mul_assoc _ _ _).symm
      _ = 0 := by rw [hg, zero_mul]
  have hzero : ∑ i ∈ t, g i • P i = 0 := by
    by_contra hne
    exact ha ⟨_, hne, hsum⟩
  have heval := congrArg (eval (k : ℂ)) hzero
  rw [eval_finsetSum, Finset.sum_eq_single k] at heval
  · rw [eval_smul, smul_eq_mul, eval_zero, hP, eval_prod] at heval
    rcases mul_eq_zero.mp heval with h | h
    · exact h
    · exfalso
      obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp h
      rw [eval_sub, eval_X, eval_C, sub_eq_zero] at hj0
      exact Finset.ne_of_mem_erase hj (Subtype.ext hj0.symm)
  · intro i _ hik
    rw [eval_smul, smul_eq_mul, hP, eval_prod,
      Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨Ne.symm hik, hk⟩) (by
        rw [eval_sub, eval_X, eval_C, sub_self]), mul_zero]
  · exact fun hk' => absurd hk hk'

/-- **Renard B.III, first step.** In a unital complex algebra of at most countable
dimension, every nonnilpotent element `a` has a nonzero scalar shift `a - z` with no
left inverse. -/
theorem nonnilpotentLeftResolvent (A : Type u) [Ring A] [Algebra ℂ A] :
    NonnilpotentLeftResolventStatement A := by
  intro hrank a ha
  by_contra hcon
  push Not at hcon
  by_cases halg : IsAlgebraic ℂ a
  · obtain ⟨q, hq, hqa⟩ := halg
    refine ha (isNilpotent_of_leftInverse_of_aeval_eq_zero hcon q.natDegree q le_rfl hq 0 ?_)
    rw [pow_zero, one_mul, hqa]
  · let s : Set ℂ := {z | z ≠ 0}
    choose b hb using fun z : s => hcon z z.2
    have hli := linearIndependent_of_leftInverse_of_transcendental halg b hb
    have hlift : Cardinal.lift.{u} (Cardinal.mk s) ≤ Cardinal.aleph0 :=
      hli.cardinal_lift_le_rank.trans (Cardinal.lift_le_aleph0.mpr hrank)
    have hs : s.Countable :=
      Cardinal.le_aleph0_iff_set_countable.mp (Cardinal.lift_le_aleph0.mp hlift)
    apply not_countable_complex
    refine (hs.insert 0).mono fun z _ => ?_
    by_cases hz : z = 0
    · exact Or.inl hz
    · exact Or.inr hz

end Langlands.Renard
