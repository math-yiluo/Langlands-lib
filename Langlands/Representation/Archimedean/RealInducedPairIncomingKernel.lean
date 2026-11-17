import Langlands.Representation.Archimedean.RealInducedPairIncomingLift
import Langlands.Representation.Archimedean.RealInducedPairKernelRecovery

/-! # The kernel before the final incoming crossing -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairIncomingKernel

open RealBlockMultiplier RealBlockFrobeniusMap RealBlockJacquet
open RealInducedPairFrobenius RealInducedPairLinkedReplacement
open RealInducedPairLinkedIncoming RealInducedPairIncomingLift
open RealInducedPairKernelRecovery

/-- The positive signed multiplier has exactly the central low modes as support. -/
theorem signedMultiplier_pos {q : ℤ} {ε : ℕ} (hq : 0 < q)
    (hp : Even (q - 1 - (ε : ℤ))) {j : ℤ} (hj : Even (j - (ε : ℤ))) :
    signedMultiplier q ε j ≠ 0 ↔ |j| < q := by
  have hc : (q.toNat : ℤ) = q := Int.toNat_of_nonneg hq.le
  have he : ((ε % 2 : ℕ) : ℤ) = 0 ∨ ((ε % 2 : ℕ) : ℤ) = 1 := by omega
  have hpar : Even ((q.toNat : ℤ) - 1 - ((ε % 2 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  have hjp : Even (j - ((ε % 2 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hj ⊢
    omega
  simpa only [signedMultiplier, ite_eq_left hq, hc] using
    binomialMultiplier_ne_zero_iff (by omega : 0 < q.toNat) he hpar hjp

/-- The negative signed multiplier has exactly the central high modes as support. -/
theorem signedMultiplier_neg {q : ℤ} {ε : ℕ} (hq : q < 0)
    (hp : Even (q - 1 - (ε : ℤ))) {j : ℤ} (hj : Even (j - (ε : ℤ))) :
    signedMultiplier q ε j ≠ 0 ↔ (q.natAbs : ℤ) < |j| := by
  have hc : (q.natAbs : ℤ) = -q := by
    rw [Int.natCast_natAbs, abs_of_neg hq]
  have he : ((ε % 2 : ℕ) : ℤ) = 0 ∨ ((ε % 2 : ℕ) : ℤ) = 1 := by omega
  have hpar : Even ((q.natAbs : ℤ) - 1 - ((ε % 2 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  have hjp : Even (j - ((ε % 2 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hj ⊢
    omega
  simpa only [signedMultiplier, ite_eq_right (not_lt.mpr hq.le), ite_eq_left hq] using
    tailMultiplier_ne_zero_iff (by omega : 0 < q.natAbs) he hpar
      (RealBlockMultiplier.neg_one_pow_sq (ε % 2)) hjp

/-- At zero the chosen generic multiplier has no zeros, including off parity. -/
theorem signedMultiplier_zero_ne (ε : ℕ) (j : ℤ) :
    signedMultiplier 0 ε j ≠ 0 := by
  have hn (m : ℕ) : (0 : ℂ) ≠ (((ε % 2 : ℕ) : ℤ) : ℂ) + 2 * m + 1 := by
    intro hm
    have hi : (0 : ℤ) = ((ε % 2 : ℕ) : ℤ) + 2 * (m : ℤ) + 1 := by
      exact_mod_cast hm
    omega
  simpa only [signedMultiplier, lt_self_iff_false, ite_false] using
    genericMultiplier_ne_zero_of_ne hn
      (ne_neg_of_re_nonneg (by simp) (by omega)) j

section Incoming

variable {d e : ComplexCharacterData} {k : ℕ}
  (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
  {μ₀ μ₂ : ℤ → ℂ}
  (hdata : MultiplierData e d (swapParameter e d)
    (signedMultiplier (innerWeight d e k) (d.weight.natAbs + 1))
    μ₀ μ₂ (lastMultiplier d e k))

include hp

theorem first_parity :
    Even (innerWeight d e k - 1 - ((d.weight.natAbs + 1 : ℕ) : ℤ)) := by
  have hs := weight_sum d e k
  rw [Int.even_iff] at hp ⊢
  omega

include hdata

/-- The negative cutoff is strictly below both original induction weights. -/
theorem to1_injective_of_inner_neg (hq : innerWeight d e k < 0) :
    Function.Injective hdata.to1 := by
  apply to1_injective_of_tail hdata (innerWeight d e k).natAbs
  · have hc : ((innerWeight d e k).natAbs : ℤ) = -innerWeight d e k := by
      rw [Int.natCast_natAbs, abs_of_neg hq]
    have hpar := first_parity hp
    rw [Int.even_iff] at hpar ⊢
    omega
  · exact fun j hj => signedMultiplier_neg hq (first_parity hp) hj
  · left
    have hc : ((innerWeight d e k).natAbs : ℤ) = -innerWeight d e k := by
      rw [Int.natCast_natAbs, abs_of_neg hq]
    have hm : min d.weight.natAbs e.weight.natAbs ≤ e.weight.natAbs := min_le_right _ _
    have hweight : innerWeight d e k =
        (k : ℤ) + 1 - (min d.weight.natAbs e.weight.natAbs : ℕ) := rfl
    omega

/-- A nonpositive signed inner weight makes the actual first crossing injective. -/
theorem to1_injective_of_inner_nonpos (hq : innerWeight d e k ≤ 0) :
    Function.Injective hdata.to1 := by
  rcases lt_or_eq_of_le hq with hneg | hzero
  · exact to1_injective_of_inner_neg hp hdata hneg
  · have hn : ∀ j : ℤ, Even (j - ((d.weight.natAbs + 1 : ℕ) : ℤ)) →
        signedMultiplier (innerWeight d e k) (d.weight.natAbs + 1) j ≠ 0 := by
      intro j _
      rw [hzero]
      exact signedMultiplier_zero_ne _ _
    exact (RealInducedPairGenericSwap.blockFrobMap_injective hdata.data1 hn).comp
      (Submodule.inclusion_injective _)

/-- For positive inner weight the exact first kernel has no central low modes. -/
theorem to1_eq_zero_iff_of_inner_pos (hq : 0 < innerWeight d e k)
    (f : KF (src e d)) :
    hdata.to1 f = 0 ↔
      ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < innerWeight d e k →
        blockFourierCoefficient 4 1 j (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  change blockFrobMap hdata.data1 (Submodule.inclusion (src_le_l0 e d) f) = 0 ↔ _
  rw [blockFrobMap_eq_zero_iff]
  constructor
  · intro hf g hg j hj
    by_cases hjp : Even (j - ((d.weight.natAbs + 1 : ℕ) : ℤ))
    · exact hf g hg j ((signedMultiplier_pos hq (first_parity hp) hjp).mpr hj)
    · exact blockFourierCoefficient_eq_zero_of_not_even
        hdata.data1.lt hdata.data1.par (Submodule.inclusion (src_le_l0 e d) f) hjp g
  · intro hf g hg j hj
    by_cases hjp : Even (j - ((d.weight.natAbs + 1 : ℕ) : ℤ))
    · exact hf g hg j ((signedMultiplier_pos hq (first_parity hp) hjp).mp hj)
    · exact blockFourierCoefficient_eq_zero_of_not_even
        hdata.data1.lt hdata.data1.par (Submodule.inclusion (src_le_l0 e d) f) hjp g

variable
  (hn0 : ∀ j : ℤ, Even (j - ((e.weight.natAbs + d.weight.natAbs + 2 : ℕ) : ℤ)) →
    μ₀ j ≠ 0)
  (hn2 : ∀ j : ℤ, Even j → μ₂ j ≠ 0)

include hn0 hn2

/-- The first three incoming crossings are injective when the inner weight is nonpositive. -/
theorem to3_injective_of_inner_nonpos (hq : innerWeight d e k ≤ 0) :
    Function.Injective hdata.to3 := by
  exact (middleEquiv hdata hn0 hn2).injective.comp
    (to1_injective_of_inner_nonpos hp hdata hq)

/-- The positive-weight kernel description survives both nonvanishing middle crossings. -/
theorem to3_eq_zero_iff_of_inner_pos (hq : 0 < innerWeight d e k)
    (f : KF (src e d)) :
    hdata.to3 f = 0 ↔
      ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < innerWeight d e k →
        blockFourierCoefficient 4 1 j (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  have heq : hdata.to3 f = 0 ↔ hdata.to1 f = 0 :=
    (middleEquiv hdata hn0 hn2).map_eq_zero_iff
  exact heq.trans (to1_eq_zero_iff_of_inner_pos hp hdata hq f)

end Incoming

end RealInducedPairIncomingKernel

open RealInducedPairFrobenius RealInducedPairLinkedReplacement
  RealInducedPairLinkedIncoming in
/-- A complete sign-based kernel description before the final incoming crossing,
retaining both original induction conditions in the source. -/
def RealInducedPairIncomingKernelStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (_h : IsLinkedAt d e k)
    (_hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))),
    ∃ μ₀ μ₂ : ℤ → ℂ,
    ∃ hdata : MultiplierData e d (swapParameter e d)
      (signedMultiplier (innerWeight d e k) (d.weight.natAbs + 1))
      μ₀ μ₂ (lastMultiplier d e k),
      (innerWeight d e k ≤ 0 →
        Function.Injective hdata.to1 ∧ Function.Injective hdata.to3) ∧
      (0 < innerWeight d e k →
        ∀ f : KF (src e d), hdata.to3 f = 0 ↔
          ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < innerWeight d e k →
            blockFourierCoefficient 4 1 j
              (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0)

open RealInducedPairIncomingKernel RealInducedPairLinkedIncoming in
theorem realInducedPairIncomingKernel : RealInducedPairIncomingKernelStatement := by
  intro d e k h hp
  obtain ⟨μ₀, μ₂, hdata, hn0, hn2⟩ := exists_multiplierData h hp
  exact ⟨μ₀, μ₂, hdata,
    fun hq => ⟨to1_injective_of_inner_nonpos hp hdata hq,
      to3_injective_of_inner_nonpos hp hdata hn0 hn2 hq⟩,
    fun hq f => to3_eq_zero_iff_of_inner_pos hp hdata hn0 hn2 hq f⟩

end Langlands.Archimedean
