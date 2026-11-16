import Langlands.Representation.Archimedean.RealBlockMultiplierNormalization
import Langlands.Representation.Archimedean.RealInducedSwapGeneric

/-!
# Parity support and opposite-parameter block operators

Internal adapters for the explicit multipliers. Restriction to the actual parity
class preserves the Frobenius map. Generic multipliers at opposite parameters
give inverse maps even when the parameter differs from the exponent difference.
-/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

namespace RealBlockMultiplier

/-- Set a multiplier to zero outside its specified parity class. -/
def parityRestrict (ε : ℤ) (μ : ℤ → ℂ) (k : ℤ) : ℂ :=
  if Even (k - ε) then μ k else 0

theorem parityRestrict_of_even {ε k : ℤ} (μ : ℤ → ℂ) (hk : Even (k - ε)) :
    parityRestrict ε μ k = μ k := by
  simp only [parityRestrict, hk, ↓reduceIte]

theorem parityRestrict_of_not_even {ε k : ℤ} (μ : ℤ → ℂ)
    (hk : ¬Even (k - ε)) : parityRestrict ε μ k = 0 := by
  simp only [parityRestrict, hk, ↓reduceIte]

theorem IsRecurrent.parityRestrict {δ : ℂ} {ε : ℤ} {μ : ℤ → ℂ}
    (h : IsRecurrent δ ε μ) : IsRecurrent δ ε (parityRestrict ε μ) := by
  intro k hk
  have hk2 : Even (k + 2 - ε) := by
    obtain ⟨r, hr⟩ := hk
    exact ⟨r + 1, by omega⟩
  rw [parityRestrict_of_even μ hk, parityRestrict_of_even μ hk2]
  exact h k hk

theorem IsSymmetric.parityRestrict {ε : ℤ} {σ : ℂ} {μ : ℤ → ℂ}
    (h : IsSymmetric ε σ μ) : IsSymmetric ε σ (parityRestrict ε μ) := by
  intro k hk
  have hkn : Even (-k - ε) := by
    obtain ⟨r, hr⟩ := hk
    exact ⟨-r - ε, by omega⟩
  rw [parityRestrict_of_even μ hk, parityRestrict_of_even μ hkn]
  exact h k hk

/-- Parity restriction turns a parity-class support bound into a bound at every
integer mode, as required by finite-multiplier cancellation. -/
theorem parityRestrict_finite {ε : ℤ} {μ : ℤ → ℂ} {L : ℕ}
    (h : ∀ k : ℤ, Even (k - ε) → (L : ℤ) ≤ |k| → μ k = 0) :
    ∀ k : ℤ, (L : ℤ) ≤ |k| → parityRestrict ε μ k = 0 := by
  intro k hk
  by_cases hp : Even (k - ε)
  · rw [parityRestrict_of_even μ hp, h k hp hk]
  · exact parityRestrict_of_not_even μ hp

theorem analyticAt_parityRestrict {ε k : ℤ} {μ : ℂ → ℤ → ℂ} {ν : ℂ}
    (h : AnalyticAt ℂ (fun z => μ z k) ν) :
    AnalyticAt ℂ (fun z => parityRestrict ε (μ z) k) ν := by
  unfold parityRestrict
  split_ifs
  · exact h
  · exact analyticAt_const

/-- At a positive exceptional parameter, the numerator at index `r` is the
first zero factor. -/
theorem genericSeq_at_positive_ne_zero_iff {ε : ℤ} (hε : 0 ≤ ε) (r m : ℕ) :
    genericSeq ((ε : ℂ) + 2 * r + 1) ε m ≠ 0 ↔ m ≤ r := by
  by_cases hm : m ≤ r
  · simp only [hm, iff_true]
    unfold genericSeq
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hir : i ≠ r := by
      have := Finset.mem_range.mp hi
      omega
    apply div_ne_zero
    · simpa only [sub_eq_add_neg] using genericSeq_denom_at_pole_ne_zero ε hir
    · simpa only [sub_neg_eq_add] using genericSeq_numer_at_pole_ne_zero hε r i
  · simp only [hm, iff_false, not_not]
    unfold genericSeq
    apply Finset.prod_eq_zero (Finset.mem_range.mpr (by omega : r < m))
    simp

/-- The unregularized positive endpoint has exactly the finite support dual to
the tail support of the regularized negative endpoint. -/
theorem genericMultiplier_at_positive_ne_zero_iff {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (r : ℕ) {k : ℤ} (hk : Even (k - ε)) :
    genericMultiplier ((ε : ℂ) + 2 * r + 1) ε k ≠ 0 ↔
      |k| < ε + 2 * (r : ℤ) + 1 := by
  rw [genericMultiplier, extend_ne_zero_iff (pow_ne_zero _ (by norm_num)),
    genericSeq_at_positive_ne_zero_iff (by omega : 0 ≤ ε), Int.abs_eq_natAbs]
  obtain ⟨s, hs⟩ := hk
  omega

theorem parityRestrict_generic_at_positive_finite {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (r : ℕ) :
    ∀ k : ℤ, ε + 2 * (r : ℤ) + 1 ≤ |k| →
      parityRestrict ε (genericMultiplier ((ε : ℂ) + 2 * r + 1) ε) k = 0 := by
  intro k hk
  by_cases hp : Even (k - ε)
  · rw [parityRestrict_of_even _ hp]
    by_contra h
    have := (genericMultiplier_at_positive_ne_zero_iff hε r hp).mp h
    omega
  · exact parityRestrict_of_not_even _ hp

theorem parityRestrict_binomial_finite {ℓ : ℕ} (hℓ : 0 < ℓ) {ε : ℤ}
    (hε : ε = 0 ∨ ε = 1) (hpar : Even ((ℓ : ℤ) - 1 - ε)) :
    ∀ k : ℤ, (ℓ : ℤ) ≤ |k| →
      parityRestrict ε (binomialMultiplier ℓ ε) k = 0 := by
  apply parityRestrict_finite
  intro k hp hk
  by_contra h
  have := (binomialMultiplier_ne_zero_iff hℓ hε hpar hp).mp h
  omega

end RealBlockMultiplier

namespace RealBlockFrobeniusMap

open Langlands.LocalFactor.Archimedean
open RealBlockMultiplier RealBlockJacquet

variable {n p : ℕ} {ds es : List RealBlock} {ε : ℤ} {σ τ : ℂ} {μ ν : ℤ → ℂ}

/-- Frobenius maps depend only on multiplier values on the source parity class. -/
theorem blockFrobMap_eq_of_eq_on_parity
    (h : IsBlockFrobData n ds es p ε σ μ) (h' : IsBlockFrobData n ds es p ε τ ν)
    (hμν : ∀ j : ℤ, Even (j - ε) → μ j = ν j) :
    blockFrobMap h = blockFrobMap h' := by
  ext f : 1
  refine eq_of_blockFourierCoefficient_eq h.lt fun j k hk => ?_
  rw [blockFourierCoefficient_blockFrobMap h _ hk,
    blockFourierCoefficient_blockFrobMap h' _ hk]
  by_cases hj : Even (j - ε)
  · rw [hμν j hj]
  · rw [blockFourierCoefficient_eq_zero_of_not_even h.lt h.par f hj k, mul_zero, mul_zero]

theorem IsBlockFrobData.parityRestrict (h : IsBlockFrobData n ds es p ε σ μ) :
    IsBlockFrobData n ds es p ε σ (RealBlockMultiplier.parityRestrict ε μ) := by
  refine { h with sym := h.sym.parityRestrict, induced_p := ?_ }
  intro d hd j hj hlow
  rw [parityRestrict_of_even μ hj]
  exact h.induced_p d hd j hj hlow

/-- Parity restriction preserves the actual map on all group points. -/
theorem blockFrobMap_parityRestrict (h : IsBlockFrobData n ds es p ε σ μ) :
    blockFrobMap h.parityRestrict = blockFrobMap h :=
  blockFrobMap_eq_of_eq_on_parity h.parityRestrict h
    (fun _ hj => parityRestrict_of_even μ hj)

/-- Pointwise reciprocal multipliers give both inverse identities. -/
theorem blockFrobMap_leftInverse
    (h : IsBlockFrobData n ds es p ε σ μ)
    (h' : IsBlockFrobData n es ds p ε τ ν)
    (hprod : ∀ j : ℤ, Even (j - ε) → ν j * μ j = 1) :
    Function.LeftInverse (blockFrobMap h') (blockFrobMap h) := by
  intro f
  exact blockFrobMap_blockFrobMap_eq h h' f fun j hj hne =>
    False.elim (hne (hprod j hj))

end RealBlockFrobeniusMap

namespace RealBlockMultiplierOperators

open Langlands.LocalFactor.Archimedean
open RealBlockMultiplier RealBlockFrobeniusMap RealCharacterPair
open RealCharacterPairReducible RealInducedSwapGeneric

variable {n : ℕ} (pre post : List RealBlock) (x y : RealCharacterData)

/-- Generic crossing data for an arbitrary parameter at fixed source and target
exponents. Only reflection symmetry is needed to construct this map. -/
theorem parameterData (ν : ℂ)
    (hr : realRank (pre ++ .character x :: .character y :: post) = n) :
    IsBlockFrobData n (pre ++ .character x :: .character y :: post)
      (pre ++ .character y :: .character x :: post) (realRank pre)
      (pairParity y x) (sigma0 y x) (genericMultiplier ν (pairParity y x)) := by
  simpa only [dc, mid_pair] using
    (data_swap (c := y) (d := x)
      (by simpa only [mid_pair] using realRank_dc_mid hr)
      (isSymmetric_genericMultiplier ν (pairParity_eq y x)))

/-- The opposite-parameter crossing is a left inverse to the forward crossing.
The statement does not require the parameter to equal the exponent difference. -/
theorem parameter_leftInverse (ν : ℂ)
    (hr : realRank (pre ++ .character x :: .character y :: post) = n)
    (hν : IsGenericParameter ν (pairParity y x)) :
    Function.LeftInverse
      (blockFrobMap (parameterData pre post y x (-ν)
        (by simpa only [mid_pair] using realRank_dc_mid hr)))
      (blockFrobMap (parameterData pre post x y ν hr)) := by
  intro f
  refine eq_of_blockFourierCoefficient_eq (parameterData pre post x y ν hr).lt
    fun j k hk => ?_
  rw [blockFourierCoefficient_blockFrobMap _ _ hk, blockFourierCoefficient_blockFrobMap _ _ hk,
    pairParity_comm x y, ← mul_assoc, mul_comm (genericMultiplier (-ν) _ j),
    genericMultiplier_mul_neg hν, one_mul]

/-- The fixed-exponent generic operator as an explicit equivalence, with the
opposite-parameter operator as its inverse. -/
def parameterEquiv (ν : ℂ)
    (hr : realRank (pre ++ .character x :: .character y :: post) = n)
    (hν : IsGenericParameter ν (pairParity y x)) :
    kFiniteFunctions (realStandardModule n (pre ++ .character x :: .character y :: post))
        (unitaryCompact ℝ n) ≃ₗ[ℂ]
      kFiniteFunctions (realStandardModule n (pre ++ .character y :: .character x :: post))
        (unitaryCompact ℝ n) :=
  { blockFrobMap (parameterData pre post x y ν hr) with
    invFun := blockFrobMap (parameterData pre post y x (-ν)
      (by simpa only [mid_pair] using realRank_dc_mid hr))
    left_inv := parameter_leftInverse pre post x y ν hr hν
    right_inv := by
      intro f
      change blockFrobMap (parameterData pre post x y ν hr)
        (blockFrobMap (parameterData pre post y x (-ν)
          (by simpa only [mid_pair] using realRank_dc_mid hr)) f) = f
      refine eq_of_blockFourierCoefficient_eq
        (parameterData pre post y x (-ν)
          (by simpa only [mid_pair] using realRank_dc_mid hr)).lt
        fun j k hk => ?_
      rw [blockFourierCoefficient_blockFrobMap _ _ hk,
        blockFourierCoefficient_blockFrobMap _ _ hk, pairParity_comm x y,
        ← mul_assoc, genericMultiplier_mul_neg hν, one_mul] }

end RealBlockMultiplierOperators

end Langlands.Archimedean
