import Langlands.GroupScheme.Examples.SU3RootQuotientJumps
import Langlands.GroupScheme.Examples.SU3RootUnitaryLattices

/-! # Indivisible central jumps in normalized quadratic coordinates -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.SU3Root

namespace Parameters

variable {L : Type v} [Field L] {c : RingInvolution L}

/-- A central coordinate jump whose half is absent from the ordinary quotient
jump set. -/
def HasIndivisibleCentralJump (ω : AddValuation L (WithTop ℝ)) : Prop :=
  ∃ r : ℝ, r ∈ centralJumpValues (c := c) ω ∧ r / 2 ∉ quotientJumpValues (c := c) ω

/-- Central jumps can equivalently be read on nonzero trace-zero second coordinates. -/
theorem mem_centralJumpValues_iff_traceZero
    (ω : AddValuation L (WithTop ℝ)) (r : ℝ) :
    r ∈ centralJumpValues (c := c) ω ↔
      ∃ y : L, y ≠ 0 ∧ y + c.bar y = 0 ∧ ω y = (r : WithTop ℝ) := by
  rw [mem_centralJumpValues_iff]
  constructor
  · rintro ⟨z, hz, hval⟩
    refine ⟨z.val.second, ?_, ?_, hval⟩
    · intro h0
      exact hz (Subtype.ext ((second_eq_zero_iff z.val).mp h0))
    · simpa only [(mem_central z.val).mp z.property, zero_mul] using z.val.equation
  · rintro ⟨y, hy, htrace, hval⟩
    let p : Parameters c := ⟨(0, y), by simpa only [zero_mul] using htrace⟩
    refine ⟨⟨p, rfl⟩, ?_, hval⟩
    intro hp
    exact hy (congrArg (fun z : central c => z.val.second) hp)

end Parameters

section Quadratic

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

local notation "σ" => conjugation K L
local notation "ι" => fieldInvolution K L

local instance : FiniteDimensional K L :=
  .of_finrank_pos (by rw [Algebra.IsQuadraticExtension.finrank_eq_two K L]; decide)

namespace IsRamifiedQuadraticValuation

variable {ω : AddValuation L (WithTop ℝ)} (hω : IsRamifiedQuadraticValuation K L ω)
include hω

/-- No central jump has its half in the ordinary quotient jump set in the
 normalized ramified case. -/
theorem half_centralJump_not_quotientJump {r : ℝ}
    (hr : r ∈ Parameters.centralJumpValues (c := ι) ω) :
    r / 2 ∉ Parameters.quotientJumpValues (c := ι) ω := by
  obtain ⟨y, hy, htrace, hyr⟩ :=
    (Parameters.mem_centralJumpValues_iff_traceZero ω r).mp hr
  obtain ⟨m, hm⟩ := hω.traceZero_parity hy htrace
  rw [hyr, WithTop.coe_eq_coe] at hm
  intro hq
  obtain ⟨x, hx, hxv⟩ := (Parameters.mem_quotientJumpValues_iff ω hω.bar_eq
    hω.traceOneMax_add (fun z hz => by rw [hω.omega_traceOneMax]; exact hω.omega_le_mu hz)
    (r / 2)).mp hq
  obtain ⟨n, hn⟩ := hω.exists_half_integer hx
  rw [hn, hω.omega_traceOneMax, halfTop_coe, ← WithTop.coe_add,
    WithTop.coe_eq_coe] at hxv
  exact int_ne_int_add_half n m (by linarith)

/-- A central jump with no ordinary half-jump exists in the normalized ramified
 case. -/
theorem exists_indivisible_centralJump :
    Parameters.HasIndivisibleCentralJump (c := ι) ω := by
  obtain ⟨r, hr⟩ := exists_omega_eq_coe ω (traceZeroElement_ne_zero K L)
  have hmem : r ∈ Parameters.centralJumpValues (c := ι) ω :=
    (Parameters.mem_centralJumpValues_iff_traceZero ω r).mpr
      ⟨traceZeroElement K L, traceZeroElement_ne_zero K L, traceZeroElement_add K L, hr⟩
  exact ⟨r, hmem, hω.half_centralJump_not_quotientJump hmem⟩

end IsRamifiedQuadraticValuation

/-- Integral values on the whole quadratic field give an attained maximum on
 trace-one elements. -/
theorem exists_maximal_traceOne_of_integer_values
    (ω : AddValuation L (WithTop ℝ)) (hinv : ∀ y : L, ω (σ y) = ω y)
    (hint : ∀ y : L, y ≠ 0 → ∃ n : ℤ, ω y = ((n : ℝ) : WithTop ℝ)) :
    ∃ t : L, t + σ t = 1 ∧ ∀ y : L, y + σ y = 1 → ω y ≤ ω t := by
  have hnonzero : ∀ y : L, y + σ y = 1 → y ≠ 0 := by
    intro y hy h0
    simp only [h0, map_zero, zero_add, zero_ne_one] at hy
  have hbound : ∀ y : L, y + σ y = 1 → ω y ≤ 0 := by
    intro y hy
    have h := ω.map_add y (σ y)
    rwa [hinv, min_self, hy, ω.map_one] at h
  obtain ⟨n, ⟨t, ht, hval⟩, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun n : ℤ => ∃ t : L, t + σ t = 1 ∧ ω t = ((n : ℝ) : WithTop ℝ))
    ⟨0, by
      rintro n ⟨t, ht, hval⟩
      have h := hbound t ht
      rw [hval, ← WithTop.coe_zero, WithTop.coe_le_coe] at h
      exact_mod_cast h⟩
    (by
      obtain ⟨n, hn⟩ := hint (traceOne K L) (hnonzero _ (traceOne_add_conjugate K L))
      exact ⟨n, traceOne K L, traceOne_add_conjugate K L, hn⟩)
  refine ⟨t, ht, fun y hy => ?_⟩
  obtain ⟨m, hm⟩ := hint y (hnonzero y hy)
  rw [hm, hval, WithTop.coe_le_coe]
  exact_mod_cast hmax m ⟨y, hy, hm⟩

/-- In the integer-valued case, two central values differing by one cannot both
 have ordinary half-jumps. -/
theorem exists_indivisible_centralJump_of_integer_values
    (ω : AddValuation L (WithTop ℝ)) (hinv : ∀ y : L, ω (σ y) = ω y)
    (hint : ∀ y : L, y ≠ 0 → ∃ n : ℤ, ω y = ((n : ℝ) : WithTop ℝ))
    (hunit : ∃ π : K, ω (algebraMap K L π) = ((1 : ℝ) : WithTop ℝ)) :
    Parameters.HasIndivisibleCentralJump (c := ι) ω := by
  obtain ⟨t, ht, hmax⟩ := exists_maximal_traceOne_of_integer_values ω hinv hint
  have ht0 : t ≠ 0 := by
    intro h0
    simp only [h0, map_zero, zero_add, zero_ne_one] at ht
  obtain ⟨m, hm⟩ := hint t ht0
  obtain ⟨d, hd⟩ := hint (traceZeroElement K L) (traceZeroElement_ne_zero K L)
  obtain ⟨π, hπ⟩ := hunit
  have hπ0 : algebraMap K L π ≠ 0 := by
    intro h0
    rw [h0, ω.map_zero] at hπ
    exact WithTop.top_ne_coe hπ
  have hmem : (d : ℝ) ∈ Parameters.centralJumpValues (c := ι) ω :=
    (Parameters.mem_centralJumpValues_iff_traceZero ω d).mpr
      ⟨traceZeroElement K L, traceZeroElement_ne_zero K L, traceZeroElement_add K L, hd⟩
  have hmem' : (d : ℝ) + 1 ∈ Parameters.centralJumpValues (c := ι) ω := by
    apply (Parameters.mem_centralJumpValues_iff_traceZero ω _).mpr
    refine ⟨algebraMap K L π * traceZeroElement K L,
      mul_ne_zero hπ0 (traceZeroElement_ne_zero K L), ?_, ?_⟩
    · change algebraMap K L π * traceZeroElement K L +
        σ (algebraMap K L π * traceZeroElement K L) = 0
      rw [map_mul, AlgEquiv.commutes, ← mul_add, traceZeroElement_add K L, mul_zero]
    · rw [ω.map_mul, hπ, hd, ← WithTop.coe_add, WithTop.coe_eq_coe]
      ring
  by_cases hq : (d : ℝ) / 2 ∈ Parameters.quotientJumpValues (c := ι) ω
  · refine ⟨(d : ℝ) + 1, hmem', ?_⟩
    intro hq'
    obtain ⟨x, hx, hxv⟩ := (Parameters.mem_quotientJumpValues_iff ω hinv ht hmax _).mp hq
    obtain ⟨x', hx', hxv'⟩ := (Parameters.mem_quotientJumpValues_iff ω hinv ht hmax _).mp hq'
    obtain ⟨n, hn⟩ := hint x hx
    obtain ⟨n', hn'⟩ := hint x' hx'
    rw [hn, hm, halfTop_coe, ← WithTop.coe_add, WithTop.coe_eq_coe] at hxv
    rw [hn', hm, halfTop_coe, ← WithTop.coe_add, WithTop.coe_eq_coe] at hxv'
    have heq : ((2 * (n' - n) : ℤ) : ℝ) = 1 := by push_cast; linarith
    have heq' : 2 * (n' - n) = 1 := by exact_mod_cast heq
    omega
  · exact ⟨d, hmem, hq⟩

end Quadratic

end Langlands.GroupScheme.SU3Root
