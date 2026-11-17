import Langlands.Representation.Archimedean.RealInducedPairIncomingKernel

/-! # The negative inner window in the outgoing linked crossings -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairOutgoingInnerWindow

open RealBlockMultiplier RealBlockFrobeniusMap RealBlockJacquet
open RealInducedPairFrobenius RealInducedPairLinkedReplacement
open RealInducedPairLinkedIncoming RealInducedPairIncomingKernel
open RealInducedPairKernelRecovery

/-- A central low-mode bound below either original weight forces a source vector
to vanish, by adjacent-rotation uncertainty. -/
theorem eq_zero_of_central_low {d e : ComplexCharacterData} (m : ℕ)
    (hm : m < d.weight.natAbs ∨ m < e.weight.natAbs) (f : KF (src d e))
    (hlow : ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, (m : ℤ) ≤ |j| →
      blockFourierCoefficient 4 1 j (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0) :
    f = 0 := by
  have hzero : ∀ g ∈ unitaryCompact ℝ 4, (f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
    rcases hm with hm | hm
    · apply RealOrthogonalBlock.adjacent_uncertainty 0 (by decide)
        (Or.inl ⟨rfl, rfl⟩) hm (continuous_coe f) f.2.2 ?_ hlow
      intro g _ j hj
      exact f.2.1.2 0 d rfl j (by simpa using hj) g
    · apply RealOrthogonalBlock.adjacent_uncertainty 1 (by decide)
        (Or.inr ⟨rfl, rfl⟩) hm (continuous_coe f) f.2.2 ?_ hlow
      intro g _ j hj
      exact f.2.1.2 2 e rfl j (by simpa using hj) g
  apply Subtype.ext
  exact eq_zero_of_mem_principalSeries_of_eqOn_unitaryCompact f.2.1.1 hzero

section Binomial

variable {d e : ComplexCharacterData} {δ : ℂ} {q : ℤ} {μ₁ μ₀ μ₂ : ℤ → ℂ}
  (hdata : MultiplierData d e δ μ₁ μ₀ μ₂
    (signedMultiplier q (d.weight.natAbs + 1)))
  (hq : 0 < q)
  (hp : Even (q - 1 - ((d.weight.natAbs + 1 : ℕ) : ℤ)))

include hdata hq hp

/-- A positive signed last multiplier has only central low modes in its output. -/
theorem to4_central_low (f : KF (src d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, q ≤ |j| →
      blockFourierCoefficient 4 1 j
        (hdata.to4 f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  intro g hg j hj
  change blockFourierCoefficient 4 1 j
    (blockFrobMap hdata.data3 (hdata.to3 f) : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0
  rw [blockFourierCoefficient_blockFrobMap hdata.data3 _ hg]
  by_cases hjp : Even (j - ((d.weight.natAbs + 1 : ℕ) : ℤ))
  · have hz : signedMultiplier q (d.weight.natAbs + 1) j = 0 := by
      by_contra hne
      have hlt := (signedMultiplier_pos hq hp hjp).mp hne
      omega
    rw [hz, zero_mul]
  · rw [blockFourierCoefficient_eq_zero_of_not_even
      hdata.data3.lt hdata.data3.par (hdata.to3 f) hjp g, mul_zero]

variable (hcut : q.toNat < d.weight.natAbs ∨ q.toNat < e.weight.natAbs)

include hcut

/-- The full four-crossing map vanishes when its last binomial cutoff is
strictly below either target induction weight. -/
theorem swap_eq_zero : hdata.swap = 0 := by
  apply LinearMap.ext
  intro f
  apply eq_zero_of_central_low q.toNat hcut.symm
  intro g hg j hj
  exact to4_central_low hdata hq hp f g hg j
    (by simpa only [Int.toNat_of_nonneg hq.le] using hj)

/-- Vanishing of the last binomial forces the preceding three-crossing output
to satisfy the central induction window at its cutoff. -/
theorem to3_inner_high (f : KF (src d e)) :
    ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ, |j| < q →
      blockFourierCoefficient 4 1 j
        (hdata.to3 f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  have hz : blockFrobMap hdata.data3 (hdata.to3 f) = 0 := by
    apply Subtype.ext
    exact congrArg (fun z : KF (dst d e) => (z : Langlands.GeneralLinear 4 ℝ → ℂ))
      (LinearMap.congr_fun (swap_eq_zero hdata hq hp hcut) f)
  have hker := (blockFrobMap_eq_zero_iff hdata.data3 (hdata.to3 f)).mp hz
  intro g hg j hj
  by_cases hjp : Even (j - ((d.weight.natAbs + 1 : ℕ) : ℤ))
  · exact hker g hg j ((signedMultiplier_pos hq hp hjp).mpr hj)
  · exact blockFourierCoefficient_eq_zero_of_not_even
      hdata.data3.lt hdata.data3.par (hdata.to3 f) hjp g

end Binomial

section Linked

variable {d e : ComplexCharacterData} {k : ℕ}
  (h : IsLinkedAt d e k)
  (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))

include h in
theorem outgoing_parameter :
    swapParameter d e = (-(outerWeight d e k : ℤ) : ℂ) + 1 := by
  have hg := RealInducedPairOuterTail.outer_gap h
  change (e.exponent + (e.weight.natAbs : ℂ) / 2) -
    (d.exponent - (d.weight.natAbs : ℂ) / 2) = _ at hg
  simp only [Int.cast_natCast]
  dsimp [swapParameter]
  linear_combination -hg

include h hp

/-- Outgoing resonant data have the signed outer tail first and the signed
negative inner weight last; both middle crossings are nonvanishing. -/
theorem exists_multiplierData :
    ∃ μ₀ μ₂ : ℤ → ℂ,
      MultiplierData d e (swapParameter d e)
        (signedMultiplier (-(outerWeight d e k : ℤ)) (e.weight.natAbs + 1))
        μ₀ μ₂ (signedMultiplier (-innerWeight d e k) (d.weight.natAbs + 1)) ∧
      (∀ j : ℤ, Even (j - ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)) →
        μ₀ j ≠ 0) ∧
      (∀ j : ℤ, Even j → μ₂ j ≠ 0) := by
  have hsum := weight_sum d e k
  have hp1 : Even (-(outerWeight d e k : ℤ) - 1 -
      ((e.weight.natAbs + 1 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  have hp3 : Even (-innerWeight d e k - 1 -
      ((d.weight.natAbs + 1 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  obtain ⟨hr1, hs1⟩ :=
    signedMultiplier_recurrent_symmetric (-(outerWeight d e k : ℤ))
      (e.weight.natAbs + 1) hp1
  obtain ⟨hr3, hs3⟩ :=
    signedMultiplier_recurrent_symmetric (-innerWeight d e k)
      (d.weight.natAbs + 1) hp3
  have hp0 : Even (-(outerWeight d e k : ℤ) + (d.weight.natAbs : ℤ) -
      ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  have hp2 : Even (-(outerWeight d e k : ℤ) + (e.weight.natAbs : ℤ) - (0 : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  obtain ⟨μ₀, hr0, hs0, hn0⟩ :=
    RealInducedPairGenericSwap.exists_multiplier
      (d.weight.natAbs + e.weight.natAbs + 2) (isGenericParameter_int _ hp0)
  obtain ⟨μ₂, hr2, hs2, hn2⟩ :=
    RealInducedPairGenericSwap.exists_multiplier 0 (isGenericParameter_int 0 hp2)
  have hc : (innerWeight d e k : ℂ) + (d.weight.natAbs : ℂ) +
      (e.weight.natAbs : ℂ) = (outerWeight d e k : ℂ) := by
    simpa only [Int.cast_add, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℂ)) hsum
  refine ⟨μ₀, μ₂, ⟨?_, hs1, ?_, hs0, ?_, ?_, ?_, hs3⟩, hn0, ?_⟩
  · rw [outgoing_parameter h]
    simpa only [Int.cast_neg] using hr1
  · convert hr0 using 1
    simp only [Int.cast_add, Int.cast_neg, Int.cast_natCast]
    rw [outgoing_parameter h]
    simp only [Int.cast_natCast]
    ring
  · convert hr2 using 1
    simp only [Int.cast_add, Int.cast_neg, Int.cast_natCast]
    rw [outgoing_parameter h]
    simp only [Int.cast_natCast]
    ring
  · simpa using hs2
  · convert hr3 using 1
    simp only [Int.cast_neg]
    rw [outgoing_parameter h]
    simp only [Int.cast_natCast]
    linear_combination hc
  · intro j hj
    exact hn2 j (by simpa using hj)

variable {μ₁ μ₀ μ₂ : ℤ → ℂ}
  (hdata : MultiplierData d e (swapParameter d e) μ₁ μ₀ μ₂
    (signedMultiplier (-innerWeight d e k) (d.weight.natAbs + 1)))

omit h hp in
theorem inner_cutoff_lt (hq : innerWeight d e k < 0) :
    (-innerWeight d e k).toNat < d.weight.natAbs ∧
      (-innerWeight d e k).toNat < e.weight.natAbs := by
  have hc : (((-innerWeight d e k).toNat : ℕ) : ℤ) = -innerWeight d e k :=
    Int.toNat_of_nonneg (by omega)
  have hweight : innerWeight d e k =
      (k : ℤ) + 1 - (min d.weight.natAbs e.weight.natAbs : ℕ) := rfl
  have hd := min_le_left d.weight.natAbs e.weight.natAbs
  have he := min_le_right d.weight.natAbs e.weight.natAbs
  omega

include hdata

omit h in
theorem negative_inner_window (hq : innerWeight d e k < 0) :
    hdata.swap = 0 ∧
      ∀ f : KF (src d e), ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ,
        |j| < (innerWeight d e k).natAbs →
          blockFourierCoefficient 4 1 j
            (hdata.to3 f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0 := by
  have hpar : Even (-innerWeight d e k - 1 -
      ((d.weight.natAbs + 1 : ℕ) : ℤ)) := by
    have hsum := weight_sum d e k
    rw [Int.even_iff] at hp ⊢
    omega
  have hcut := (inner_cutoff_lt (d := d) (e := e) hq).1
  refine ⟨swap_eq_zero hdata (by omega) hpar (Or.inl hcut), ?_⟩
  intro f g hg j hj
  apply to3_inner_high hdata (by omega) hpar (Or.inl hcut) f g hg j
  simpa only [Int.natCast_natAbs, abs_of_neg hq] using hj

end Linked

end RealInducedPairOutgoingInnerWindow

open RealInducedPairFrobenius RealInducedPairLinkedReplacement
  RealInducedPairLinkedIncoming in
/-- Outgoing data at a negative signed inner weight give a zero full map and
the actual inner induction window after their first three crossings. -/
def RealInducedPairOutgoingInnerWindowStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (_h : IsLinkedAt d e k)
    (_hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))),
    ∃ μ₀ μ₂ : ℤ → ℂ,
    ∃ hdata : MultiplierData d e (swapParameter d e)
      (signedMultiplier (-(outerWeight d e k : ℤ)) (e.weight.natAbs + 1))
      μ₀ μ₂ (signedMultiplier (-innerWeight d e k) (d.weight.natAbs + 1)),
      (∀ j : ℤ, Even (j - ((d.weight.natAbs + e.weight.natAbs + 2 : ℕ) : ℤ)) →
        μ₀ j ≠ 0) ∧
      (∀ j : ℤ, Even j → μ₂ j ≠ 0) ∧
      (innerWeight d e k < 0 →
        hdata.swap = 0 ∧
        ∀ f : KF (src d e), ∀ g ∈ unitaryCompact ℝ 4, ∀ j : ℤ,
          |j| < (innerWeight d e k).natAbs →
            blockFourierCoefficient 4 1 j
              (hdata.to3 f : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0)

open RealInducedPairOutgoingInnerWindow in
theorem realInducedPairOutgoingInnerWindow :
    RealInducedPairOutgoingInnerWindowStatement := by
  intro d e k h hp
  obtain ⟨μ₀, μ₂, hdata, hn0, hn2⟩ := exists_multiplierData h hp
  exact ⟨μ₀, μ₂, hdata, hn0, hn2, negative_inner_window hp hdata⟩

end Langlands.Archimedean
