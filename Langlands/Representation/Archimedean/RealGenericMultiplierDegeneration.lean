import Langlands.Representation.Archimedean.RealBlockMultiplierNormalization

/-! # Exact binomial and canonical-tail degenerations of generic multipliers -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.RealGenericMultiplierDegeneration

open RealBlockMultiplier

variable {ℓ : ℕ} {ε : ℤ}

/-- The positive resonant generic sequence is the binomial sequence normalized at zero. -/
theorem binomialSeq_eq_generic
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) (m : ℕ) :
    binomialSeq ℓ ε 0 * genericSeq (ℓ : ℂ) ε m = binomialSeq ℓ ε m := by
  obtain ⟨r, hl, he⟩ := exists_half hℓ hε hpar
  induction m with
  | zero => simp [genericSeq]
  | succ m ih =>
      have hν : 0 < (ℓ : ℂ).re := by simpa using (show (0 : ℝ) < ℓ by exact_mod_cast hℓ)
      have hd := genericSeq_denom_ne_zero hν (show 0 ≤ ε by omega) m
      apply mul_right_cancel₀ hd
      have hg := genericSeq_succ hν (show 0 ≤ ε by omega) m
      have hb := binomialSeq_succ hl he m
      linear_combination binomialSeq ℓ ε 0 * hg - hb +
        ((ε : ℂ) + 2 * m + 2 - ((ℓ : ℂ) + 1)) * ih

theorem binomial_base_ne_zero
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) : binomialSeq ℓ ε 0 ≠ 0 := by
  obtain ⟨r, hl, _⟩ := exists_half hℓ hε hpar
  exact (binomialSeq_ne_zero_iff hl 0).mpr (Nat.zero_le r)

theorem binomialMultiplier_eq_generic
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1)
    (hpar : Even ((ℓ : ℤ) - 1 - ε)) (j : ℤ) :
    binomialMultiplier ℓ ε j = binomialSeq ℓ ε 0 * genericMultiplier (ℓ : ℂ) ε j := by
  simp only [binomialMultiplier, genericMultiplier, extend]
  split_ifs
  · exact (binomialSeq_eq_generic hℓ hε hpar _).symm
  · rw [← binomialSeq_eq_generic hℓ hε hpar (j.natAbs / 2)]
    ring

/-- The regularized value at the negative pole is the tail sequence normalized at its
first nonzero index. -/
theorem regularizedSeq_eq_tail (hε : ε = 0 ∨ ε = 1) (r : ℕ)
    (hl : ℓ = ε.toNat + 2 * r + 1) (m : ℕ) :
    regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r m =
      regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r (r + 1) * tailSeq ℓ ε m := by
  have he : (ε.toNat : ℤ) = ε := Int.toNat_of_nonneg (by omega)
  have hec : (ε.toNat : ℂ) = ε := by exact_mod_cast he
  have hc : (ℓ : ℂ) = (ε : ℂ) + 2 * r + 1 := by
    rw [hl]
    push_cast
    rw [hec]
  have ht0 (n : ℕ) (hn : n ≤ r) : tailSeq ℓ ε n = 0 := by
    apply not_ne_iff.mp
    rw [tailSeq_ne_zero_iff hl]
    omega
  have ht1 : tailSeq ℓ ε (r + 1) = 1 := by
    rw [tailSeq_eq hl, show r + 1 + ε.toNat + r = ℓ by omega,
      Nat.choose_self, Nat.cast_one]
  induction m with
  | zero =>
      rw [regularizedSeq_at_pole_eq_zero ε (Nat.zero_le r), ht0 0 (Nat.zero_le r), mul_zero]
  | succ m ih =>
      rcases lt_trichotomy m r with hm | rfl | hm
      · rw [regularizedSeq_at_pole_eq_zero ε (by omega), ht0 (m + 1) (by omega), mul_zero]
      · rw [ht1, mul_one]
      · have hd : -((ε : ℂ) + 2 * r + 1) + 1 + ε + 2 * m ≠ 0 := by
          intro hz
          have hmr : (m : ℂ) = r := by linear_combination hz / 2
          exact (ne_of_gt hm) (by exact_mod_cast hmr)
        apply mul_right_cancel₀ hd
        have hg := regularizedSeq_at_pole_succ ε r m
        have ht := tailSeq_succ hl he m
        rw [hc] at ht
        linear_combination hg -
          regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r (r + 1) * ht +
          ((ε : ℂ) + 2 * m + 2 - (-((ε : ℂ) + 2 * r + 1) + 1)) * ih

theorem regularized_base_ne_zero (hε : ε = 0 ∨ ε = 1) (r : ℕ) :
    regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r (r + 1) ≠ 0 :=
  (regularizedSeq_at_pole_ne_zero_iff (show 0 ≤ ε by omega) r (r + 1)).mpr (Nat.lt_succ_self r)

theorem regularizedMultiplier_eq_tail (hε : ε = 0 ∨ ε = 1) (r : ℕ)
    (hl : ℓ = ε.toNat + 2 * r + 1) (j : ℤ) :
    regularizedMultiplier (-((ε : ℂ) + 2 * r + 1)) ε r j =
      regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r (r + 1) *
        tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j := by
  simp only [regularizedMultiplier, tailMultiplier, extend]
  split_ifs
  · exact regularizedSeq_eq_tail hε r hl _
  · rw [regularizedSeq_eq_tail hε r hl (j.natAbs / 2)]
    ring

theorem analyticAt_genericMultiplier_pos
    (hℓ : 0 < ℓ) (hε : ε = 0 ∨ ε = 1) (j : ℤ) :
    AnalyticAt ℂ (fun z => genericMultiplier z ε j) (ℓ : ℂ) := by
  have hν : 0 < (ℓ : ℂ).re := by simpa using (show (0 : ℝ) < ℓ by exact_mod_cast hℓ)
  have hs := analyticAt_genericSeq ε (j.natAbs / 2)
    (fun i _ => genericSeq_denom_ne_zero hν (show 0 ≤ ε by omega) i)
  unfold genericMultiplier extend
  split_ifs
  · exact hs
  · exact analyticAt_const.mul hs

end Langlands.Archimedean.RealGenericMultiplierDegeneration

namespace Langlands.Archimedean

open RealBlockMultiplier in
/-- Positive resonant evaluation gives the binomial, and negative-pole regularization
gives the canonical high tail, in each case up to a nonzero displayed scalar. -/
def RealGenericMultiplierDegenerationStatement : Prop :=
  ∀ (ℓ : ℕ) (ε : ℤ), 0 < ℓ → (ε = 0 ∨ ε = 1) →
    Even ((ℓ : ℤ) - 1 - ε) →
      ∃ B : ℂ, B ≠ 0 ∧
        (∀ j : ℤ, binomialMultiplier ℓ ε j = B * genericMultiplier (ℓ : ℂ) ε j ∧
          AnalyticAt ℂ (fun z => genericMultiplier z ε j) (ℓ : ℂ)) ∧
        ∀ r : ℕ, ℓ = ε.toNat + 2 * r + 1 →
          ∃ T : ℂ, T ≠ 0 ∧ ∀ j : ℤ,
            regularizedMultiplier (-((ε : ℂ) + 2 * r + 1)) ε r j =
              T * tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j ∧
            AnalyticAt ℂ (fun z => regularizedMultiplier z ε r j)
              (-((ε : ℂ) + 2 * r + 1))

theorem realGenericMultiplierDegeneration : RealGenericMultiplierDegenerationStatement := by
  intro ℓ ε hℓ hε hpar
  refine ⟨RealBlockMultiplier.binomialSeq ℓ ε 0,
    RealGenericMultiplierDegeneration.binomial_base_ne_zero hℓ hε hpar, ?_, ?_⟩
  · intro j
    exact ⟨RealGenericMultiplierDegeneration.binomialMultiplier_eq_generic hℓ hε hpar j,
      RealGenericMultiplierDegeneration.analyticAt_genericMultiplier_pos hℓ hε j⟩
  · intro r hl
    refine ⟨RealBlockMultiplier.regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r (r + 1),
      RealGenericMultiplierDegeneration.regularized_base_ne_zero hε r, ?_⟩
    intro j
    exact ⟨RealGenericMultiplierDegeneration.regularizedMultiplier_eq_tail hε r hl j,
      RealBlockMultiplier.analyticAt_regularizedMultiplier_at_pole ε j r⟩

end Langlands.Archimedean
