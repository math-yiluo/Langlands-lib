import Langlands.GroupScheme.Unipotent.PrincipalPart
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.FieldTheory.Galois.Infinite

/-! # Galois descent of zeros of additive principal forms -/

noncomputable section

universe u v w

open Polynomial
open scoped BigOperators

namespace Langlands.GroupScheme.Unipotent

variable {k : Type u} [Field k] {K : Type v} [Field K] [Algebra k K]
  {ι : Type w} [Fintype ι]

/-- A sum of single exponential-characteristic powers vanishes only at zero. -/
def HasAnisotropicPowerSum (p : ℕ) (c : ι → k) (m : ι → ℕ) : Prop :=
  ∀ b : ι → k, (∑ i, c i * b i ^ (p ^ m i)) = 0 → b = 0

/-- Anisotropy of an additive principal form is preserved by every algebraic
Galois extension, with no finiteness assumption on the extension. -/
theorem HasAnisotropicPowerSum.of_isGalois
    (p : ℕ) [ExpChar k p] [IsGalois k K] {c : ι → k} {m : ι → ℕ}
    (ha : HasAnisotropicPowerSum p c m) :
    HasAnisotropicPowerSum p (fun i => algebraMap k K (c i)) m := by
  classical
  have : ExpChar K p := expChar_of_injective_algebraMap (algebraMap k K).injective p
  have descend : ∀ s : Finset ι, ∀ b : ι → K,
      (∀ i, i ∉ s → b i = 0) →
      (∑ i, algebraMap k K (c i) * b i ^ (p ^ m i)) = 0 → b = 0 := by
    intro s
    induction s using Finset.strongInductionOn with
    | _ s ih =>
      intro b hsupport hb
      by_cases hs : s.Nonempty
      · obtain ⟨j, hjs, hjmax⟩ := Finset.exists_mem_eq_sup s hs m
        have hm (i : ι) (hi : i ∈ s) : m i ≤ m j := by
          rw [← hjmax]
          exact Finset.le_sup hi
        have hproper : s.erase j ⊂ s := Finset.erase_ssubset hjs
        by_cases hbj : b j = 0
        · apply ih (s.erase j) hproper b
          · intro i hi
            by_cases hij : i = j
            · simpa [hij] using hbj
            · exact hsupport i (fun his => hi (Finset.mem_erase.mpr ⟨hij, his⟩))
          · exact hb
        · let a : ι → K := fun i => b i / b j ^ (p ^ (m j - m i))
          have haj : a j = 1 := by simp [a, hbj]
          have hasupport (i : ι) (hi : i ∉ s) : a i = 0 := by
            simp [a, hsupport i hi]
          have haeq : (∑ i, algebraMap k K (c i) * a i ^ (p ^ m i)) = 0 := by
            calc
              (∑ i, algebraMap k K (c i) * a i ^ (p ^ m i)) =
                  ∑ i, (algebraMap k K (c i) * b i ^ (p ^ m i)) /
                    b j ^ (p ^ m j) := by
                apply Finset.sum_congr rfl
                intro i _
                by_cases hi : i ∈ s
                · have hexp : p ^ (m j - m i) * p ^ m i = p ^ m j := by
                    rw [← pow_add, Nat.sub_add_cancel (hm i hi)]
                  simp only [a, div_pow, ← pow_mul, hexp, mul_div_assoc]
                · simp [hasupport i hi, hsupport i hi,
                    zero_pow (pow_ne_zero (m i) (expChar_ne_zero k p))]
              _ = (∑ i, algebraMap k K (c i) * b i ^ (p ^ m i)) /
                  b j ^ (p ^ m j) := by simp only [div_eq_mul_inv, Finset.sum_mul]
              _ = 0 := by rw [hb, zero_div]
          have hafixed (σ : K ≃ₐ[k] K) : ∀ i, σ (a i) = a i := by
            have hσ : (∑ i, algebraMap k K (c i) * (σ (a i)) ^ (p ^ m i)) = 0 := by
              simpa only [map_sum, map_mul, map_pow, AlgEquiv.commutes, map_zero]
                using congrArg σ haeq
            have hdiff :
                (∑ i, algebraMap k K (c i) * (a i - σ (a i)) ^ (p ^ m i)) = 0 := by
              simp only [sub_pow_expChar_pow, mul_sub, Finset.sum_sub_distrib]
              rw [haeq, hσ, sub_self]
            have hzero : (fun i => a i - σ (a i)) = 0 := by
              apply ih (s.erase j) hproper _ _ hdiff
              intro i hi
              by_cases hij : i = j
              · subst i
                simp [haj]
              · have his : i ∉ s := fun his => hi (Finset.mem_erase.mpr ⟨hij, his⟩)
                simp [hasupport i his]
            intro i
            exact (sub_eq_zero.mp (congrFun hzero i)).symm
          have halift (i : ι) : ∃ x : k, algebraMap k K x = a i :=
            (InfiniteGalois.mem_range_algebraMap_iff_fixed (a i)).mpr (fun σ => hafixed σ i)
          choose x hx using halift
          have hxzero : (∑ i, c i * x i ^ (p ^ m i)) = 0 := by
            apply (algebraMap k K).injective
            simpa only [map_sum, map_mul, map_pow, hx, map_zero] using haeq
          have hxall : x = 0 := ha x hxzero
          have : a j = 0 := by rw [← hx j, show x j = 0 from congrFun hxall j, map_zero]
          exact False.elim (one_ne_zero (haj.symm.trans this))
      · ext i
        exact hsupport i (by simp [Finset.not_nonempty_iff_eq_empty.mp hs])
  intro b hb
  exact descend Finset.univ b (by simp) hb

/-- An additive principal form has a nonzero zero over a Galois extension
exactly when it has one over the coefficient field. -/
theorem exists_nonzero_powerSum_zero_iff_of_isGalois
    (p : ℕ) [ExpChar k p] [IsGalois k K] (c : ι → k) (m : ι → ℕ) :
    (∃ b : ι → K, b ≠ 0 ∧
      (∑ i, algebraMap k K (c i) * b i ^ (p ^ m i)) = 0) ↔
    (∃ b : ι → k, b ≠ 0 ∧ (∑ i, c i * b i ^ (p ^ m i)) = 0) := by
  constructor
  · rintro ⟨b, hb, heq⟩
    by_contra h
    have ha : HasAnisotropicPowerSum p c m := by
      intro a heq
      by_contra ha
      exact h ⟨a, ha, heq⟩
    exact hb (ha.of_isGalois p b heq)
  · rintro ⟨b, hb, heq⟩
    refine ⟨fun i => algebraMap k K (b i), ?_, ?_⟩
    · intro hz
      apply hb
      funext i
      apply (algebraMap k K).injective
      simpa only [Pi.zero_apply, map_zero] using congrFun hz i
    · simpa only [map_sum, map_mul, map_pow, map_zero]
        using congrArg (algebraMap k K) heq

/-- The polynomial principal-part predicate is preserved by Galois extension
when all coordinate degrees are powers of the exponential characteristic. -/
theorem HasAnisotropicPrincipalPart.map_of_isGalois
    (p : ℕ) [ExpChar k p] [IsGalois k K] {f : ι → k[X]}
    (ha : HasAnisotropicPrincipalPart f) (m : ι → ℕ)
    (hm : ∀ i, (f i).natDegree = p ^ m i) :
    HasAnisotropicPrincipalPart (fun i => (f i).map (algebraMap k K)) := by
  have ha' : HasAnisotropicPowerSum p (fun i => (f i).leadingCoeff) m := by
    simpa only [HasAnisotropicPowerSum, HasAnisotropicPrincipalPart, hm] using ha
  have haK := ha'.of_isGalois (K := K) p
  simpa only [HasAnisotropicPowerSum, HasAnisotropicPrincipalPart,
    Polynomial.leadingCoeff_map_of_injective (algebraMap k K).injective,
    Polynomial.natDegree_map_eq_of_injective (algebraMap k K).injective, hm] using haK

end Langlands.GroupScheme.Unipotent
