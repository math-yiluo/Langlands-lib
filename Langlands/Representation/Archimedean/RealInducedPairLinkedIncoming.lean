import Langlands.Representation.Archimedean.RealInducedPairOuterTail
import Langlands.Representation.Archimedean.RealInducedPairGenericSwap

/-! # The incoming four-crossing complex at a linked induced pair -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean

namespace RealInducedPairLinkedIncoming

open RealBlockMultiplier RealSwapLandingMirror RealInducedPairFrobenius
open RealInducedPairLinkedReplacement RealBlockFrobeniusMap RealStandardFiltration

/-- A resonant multiplier at a signed integral parameter, using the nonzero generic
zero-parameter multiplier when the signed weight is zero. -/
def signedMultiplier (q : ℤ) (ε : ℕ) : ℤ → ℂ :=
  if 0 < q then binomialMultiplier q.toNat ((ε % 2 : ℕ) : ℤ)
  else if q < 0 then
    tailMultiplier q.natAbs ((ε % 2 : ℕ) : ℤ) ((-1 : ℂ) ^ (ε % 2))
  else genericMultiplier 0 ((ε % 2 : ℕ) : ℤ)

theorem signedMultiplier_recurrent_symmetric (q : ℤ) (ε : ℕ)
    (hp : Even (q - 1 - (ε : ℤ))) :
    IsRecurrent ((q : ℂ) + 1) (ε : ℤ) (signedMultiplier q ε) ∧
      IsSymmetric (ε : ℤ) ((-1 : ℂ) ^ ε) (signedMultiplier q ε) := by
  have hε : ((ε % 2 : ℕ) : ℤ) = 0 ∨ ((ε % 2 : ℕ) : ℤ) = 1 := by omega
  have hpar : Even (q - 1 - ((ε % 2 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  have he : Even (((ε % 2 : ℕ) : ℤ) - (ε : ℤ)) := by
    rw [Int.even_iff]
    omega
  have hs : (-1 : ℂ) ^ (ε % 2) = (-1 : ℂ) ^ ε :=
    RealSwapLandingMirror.neg_one_pow_congr (by omega)
  suffices hr :
      IsRecurrent ((q : ℂ) + 1) ((ε % 2 : ℕ) : ℤ) (signedMultiplier q ε) ∧
        IsSymmetric ((ε % 2 : ℕ) : ℤ) ((-1 : ℂ) ^ (ε % 2))
          (signedMultiplier q ε) from
    ⟨isRecurrent_congr hr.1 he, isSymmetric_congr hr.2 he hs⟩
  by_cases hq : 0 < q
  · have hcast : (q.toNat : ℤ) = q := Int.toNat_of_nonneg (by omega)
    have hc : (q.toNat : ℂ) = (q : ℂ) := by exact_mod_cast hcast
    have hpos : 0 < q.toNat := by omega
    have hp' : Even ((q.toNat : ℤ) - 1 - ((ε % 2 : ℕ) : ℤ)) := by
      rwa [hcast]
    simp only [signedMultiplier, ite_eq_left hq]
    exact ⟨by simpa only [hc] using isRecurrent_binomialMultiplier hpos hε hp',
      by simpa only [Int.natAbs_natCast] using isSymmetric_binomialMultiplier q.toNat hε⟩
  · by_cases hneg : q < 0
    · have hcast : (q.natAbs : ℤ) = -q := by
        rw [Int.natCast_natAbs, abs_of_neg hneg]
      have hc : (q.natAbs : ℂ) = -(q : ℂ) := by
        simpa only [Int.cast_natCast, Int.cast_neg] using
          congrArg (fun z : ℤ => (z : ℂ)) hcast
      have hpos : 0 < q.natAbs := by omega
      have hp' : Even ((q.natAbs : ℤ) - 1 - ((ε % 2 : ℕ) : ℤ)) := by
        rw [Int.even_iff] at hpar ⊢
        omega
      have hsg : ((-1 : ℂ) ^ (ε % 2)) ^ 2 = 1 := neg_one_pow_sq _
      simp only [signedMultiplier, ite_eq_right hq, ite_eq_left hneg]
      exact ⟨by
        convert isRecurrent_tailMultiplier hpos hε hp' hsg using 1
        rw [hc]
        ring,
        isSymmetric_tailMultiplier hpos hε hp' hsg⟩
    · have hzero : q = 0 := by omega
      subst q
      simp only [signedMultiplier, lt_self_iff_false, ite_false]
      exact ⟨by
        simpa only [Int.cast_zero, zero_add] using
          isRecurrent_genericMultiplier_of_ne (ν := 0) hε
            (ne_neg_of_re_nonneg (by simp) (by omega)),
        by simpa only [Int.natAbs_natCast] using isSymmetric_genericMultiplier 0 hε⟩

/-- The opposite parity to the rank-one singular set is generic, for either sign
of the integral parameter. -/
theorem isGenericParameter_int {q : ℤ} (ε : ℕ) (hp : Even (q - (ε : ℤ))) :
    IsGenericParameter (q : ℂ) ((ε % 2 : ℕ) : ℤ) := by
  constructor
  · intro m hm
    have hi : q = ((ε % 2 : ℕ) : ℤ) + 2 * (m : ℤ) + 1 := by
      exact_mod_cast hm
    rw [Int.even_iff] at hp
    omega
  · intro m hm
    have hi : q = -(((ε % 2 : ℕ) : ℤ) + 2 * (m : ℤ) + 1) := by
      exact_mod_cast hm
    rw [Int.even_iff] at hp
    omega

theorem weight_sum (d e : ComplexCharacterData) (k : ℕ) :
    innerWeight d e k + (d.weight.natAbs : ℤ) + (e.weight.natAbs : ℤ) =
      (outerWeight d e k : ℤ) := by
  have hm := max_add_min d.weight.natAbs e.weight.natAbs
  unfold innerWeight outerWeight
  omega

theorem incoming_parameter {d e : ComplexCharacterData} {k : ℕ}
    (h : IsLinkedAt d e k) :
    swapParameter e d = (innerWeight d e k : ℂ) + 1 := by
  obtain ⟨-, -, h3, h4⟩ := endpoint_equalities h
  dsimp [swapParameter]
  linear_combination -h3 + h4

/-- The last crossing is the central low-mode binomial of the original source. -/
abbrev lastMultiplier (d e : ComplexCharacterData) (k : ℕ) : ℤ → ℂ :=
  binomialMultiplier (outerWeight d e k) (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ)

theorem exists_multiplierData {d e : ComplexCharacterData} {k : ℕ}
    (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))) :
    ∃ μ₀ μ₂ : ℤ → ℂ,
      MultiplierData e d (swapParameter e d)
        (signedMultiplier (innerWeight d e k) (d.weight.natAbs + 1))
        μ₀ μ₂ (lastMultiplier d e k) ∧
      (∀ j : ℤ, Even (j - ((e.weight.natAbs + d.weight.natAbs + 2 : ℕ) : ℤ)) →
        μ₀ j ≠ 0) ∧
      (∀ j : ℤ, Even j → μ₂ j ≠ 0) := by
  have hsum := weight_sum d e k
  have hp1 : Even (innerWeight d e k - 1 - ((d.weight.natAbs + 1 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  obtain ⟨hr1, hs1⟩ :=
    signedMultiplier_recurrent_symmetric (innerWeight d e k) (d.weight.natAbs + 1) hp1
  have hp0 : Even (innerWeight d e k + (e.weight.natAbs : ℤ) -
      ((e.weight.natAbs + d.weight.natAbs + 2 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  have hp2 : Even (innerWeight d e k + (d.weight.natAbs : ℤ) - (0 : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  obtain ⟨μ₀, hr0, hs0, hn0⟩ :=
    RealInducedPairGenericSwap.exists_multiplier
      (e.weight.natAbs + d.weight.natAbs + 2) (isGenericParameter_int _ hp0)
  obtain ⟨μ₂, hr2, hs2, hn2⟩ :=
    RealInducedPairGenericSwap.exists_multiplier 0 (isGenericParameter_int 0 hp2)
  have he3 : (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) = 0 ∨
      (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) = 1 := by omega
  have hp3 : Even ((outerWeight d e k : ℤ) - 1 -
      (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ)) := by
    rw [Int.even_iff] at hp ⊢
    omega
  have hr3 := isRecurrent_binomialMultiplier
    (RealInducedPairOuterTail.outerWeight_pos d e k) he3 hp3
  have hs3 := isSymmetric_binomialMultiplier (outerWeight d e k) he3
  have he : Even ((((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) -
      ((e.weight.natAbs + 1 : ℕ) : ℤ)) := by
    rw [Int.even_iff]
    omega
  have hc : (innerWeight d e k : ℂ) + (d.weight.natAbs : ℂ) +
      (e.weight.natAbs : ℂ) = (outerWeight d e k : ℂ) := by
    simpa only [Int.cast_add, Int.cast_natCast] using
      congrArg (fun z : ℤ => (z : ℂ)) hsum
  refine ⟨μ₀, μ₂, ⟨?_, hs1, ?_, hs0, ?_, ?_, ?_, ?_⟩, hn0, ?_⟩
  · rwa [incoming_parameter h]
  · convert hr0 using 1
    simp only [Int.cast_add, Int.cast_natCast]
    rw [incoming_parameter h]
    ring
  · convert hr2 using 1
    simp only [Int.cast_add, Int.cast_natCast]
    rw [incoming_parameter h]
    ring
  · simpa using hs2
  · convert isRecurrent_congr hr3 he using 1
    rw [incoming_parameter h]
    linear_combination hc
  · exact isSymmetric_congr
      (by simpa only [Int.natAbs_natCast] using hs3) he
      (RealSwapLandingMirror.neg_one_pow_congr (by omega))
  · intro j hj
    exact hn2 j (by simpa using hj)

/-- The last binomial crossing forces every incoming output into the outer-tail
kernel of the actual two-window source. -/
theorem outerMap_swap_eq_zero {d e : ComplexCharacterData} {k : ℕ}
    (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
    {μ₁ μ₀ μ₂ : ℤ → ℂ}
    (hdata : MultiplierData e d (swapParameter e d) μ₁ μ₀ μ₂ (lastMultiplier d e k))
    (f : RealInducedPairFrobenius.KF (src e d)) :
    RealInducedPairOuterTail.outerMap h hp (hdata.swap f) = 0 := by
  apply (RealInducedPairOuterTail.outerMap_eq_zero_iff h hp _).mpr
  intro g hg j hj
  change blockFourierCoefficient 4 1 j
    (blockFrobMap hdata.data3 (hdata.to3 f) : Langlands.GeneralLinear 4 ℝ → ℂ) g = 0
  rw [blockFourierCoefficient_blockFrobMap hdata.data3 _ hg]
  by_cases hjp : Even (j - ((e.weight.natAbs + 1 : ℕ) : ℤ))
  · have he : (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) = 0 ∨
        (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ) = 1 := by omega
    have hpar : Even ((outerWeight d e k : ℤ) - 1 -
        (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ)) := by
      rw [Int.even_iff] at hp ⊢
      omega
    have hjp' : Even (j - (((e.weight.natAbs + 1) % 2 : ℕ) : ℤ)) := by
      rw [Int.even_iff] at hjp ⊢
      omega
    have hz : lastMultiplier d e k j = 0 := by
      by_contra hne
      have hlt := (binomialMultiplier_ne_zero_iff
        (RealInducedPairOuterTail.outerWeight_pos d e k) he hpar hjp').mp hne
      omega
    rw [hz, zero_mul]
  · rw [RealBlockJacquet.blockFourierCoefficient_eq_zero_of_not_even
      hdata.data3.lt hdata.data3.par (hdata.to3 f) hjp g, mul_zero]

theorem outerMap_comp_swap {d e : ComplexCharacterData} {k : ℕ}
    (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
    {μ₁ μ₀ μ₂ : ℤ → ℂ}
    (hdata : MultiplierData e d (swapParameter e d) μ₁ μ₀ μ₂ (lastMultiplier d e k)) :
    (RealInducedPairOuterTail.outerMap h hp).comp hdata.swap = 0 := by
  apply LinearMap.ext
  intro f
  exact outerMap_swap_eq_zero h hp hdata f

theorem range_swap_le_ker {d e : ComplexCharacterData} {k : ℕ}
    (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ)))
    {μ₁ μ₀ μ₂ : ℤ → ℂ}
    (hdata : MultiplierData e d (swapParameter e d) μ₁ μ₀ μ₂ (lastMultiplier d e k)) :
    LinearMap.range hdata.swap ≤ LinearMap.ker (RealInducedPairOuterTail.outerMap h hp) := by
  rintro f ⟨g, rfl⟩
  exact outerMap_swap_eq_zero h hp hdata g

end RealInducedPairLinkedIncoming

open RealInducedPairLinkedIncoming RealInducedPairFrobenius
  RealInducedPairLinkedReplacement in
/-- At the canonical linked resonance, the specified incoming four-crossing map
and the actual outer tail form a complex. -/
def RealInducedPairLinkedIncomingStatement : Prop :=
  ∀ (d e : ComplexCharacterData) (k : ℕ) (h : IsLinkedAt d e k)
    (hp : Even ((outerWeight d e k : ℤ) - (e.weight.natAbs : ℤ))),
    ∃ μ₀ μ₂ : ℤ → ℂ,
    ∃ hdata : MultiplierData e d (swapParameter e d)
      (signedMultiplier (innerWeight d e k) (d.weight.natAbs + 1))
      μ₀ μ₂ (lastMultiplier d e k),
      (∀ j : ℤ, Even (j - ((e.weight.natAbs + d.weight.natAbs + 2 : ℕ) : ℤ)) →
        μ₀ j ≠ 0) ∧
      (∀ j : ℤ, Even j → μ₂ j ≠ 0) ∧
      IsRealIntertwinerModulo 4 (src e d) (src d e) ⊥ hdata.swap ∧
      (RealInducedPairOuterTail.outerMap h hp).comp hdata.swap = 0 ∧
      LinearMap.range hdata.swap ≤ LinearMap.ker (RealInducedPairOuterTail.outerMap h hp)

open RealInducedPairLinkedIncoming in
theorem realInducedPairLinkedIncoming : RealInducedPairLinkedIncomingStatement := by
  intro d e k h hp
  obtain ⟨μ₀, μ₂, hdata, hn0, hn2⟩ := exists_multiplierData h hp
  exact ⟨μ₀, μ₂, hdata, hn0, hn2, hdata.swap_isRealIntertwinerModulo ⊥,
    outerMap_comp_swap h hp hdata, range_swap_le_ker h hp hdata⟩

end Langlands.Archimedean
