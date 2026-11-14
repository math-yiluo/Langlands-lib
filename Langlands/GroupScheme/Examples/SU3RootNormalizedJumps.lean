import Langlands.GroupScheme.Examples.SU3RootJumpParity

/-! # Indivisible jumps for base-normalized quadratic valuations -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.SU3Root

section Quadratic

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [Algebra.IsQuadraticExtension K L] [Algebra.IsSeparable K L]

local notation "σ" => conjugation K L

/-- Conjugation invariance, integer base values, and an attained base value one. -/
structure IsNormalizedQuadraticValuation (ω : AddValuation L (WithTop ℝ)) : Prop where
  conjugation_eq : ∀ z : L, ω (σ z) = ω z
  base_int : ∀ a : K, a ≠ 0 → ∃ n : ℤ, ω (algebraMap K L a) = ((n : ℝ) : WithTop ℝ)
  exists_one : ∃ π : K, ω (algebraMap K L π) = ((1 : ℝ) : WithTop ℝ)

variable {K L}

namespace IsNormalizedQuadraticValuation

variable {ω : AddValuation L (WithTop ℝ)} (hω : IsNormalizedQuadraticValuation K L ω)
include hω

/-- The quadratic norm forces every nonzero value to be a half-integer. -/
theorem exists_half_integer {x : L} (hx : x ≠ 0) :
    ∃ n : ℤ, ω x = (((n : ℝ) / 2 : ℝ) : WithTop ℝ) := by
  obtain ⟨a, ha⟩ := exists_algebraMap_eq_of_conjugation_eq K L (x := x * σ x)
    (by rw [map_mul, conjugation_involutive K L x, mul_comm])
  have hσx : σ x ≠ 0 := by
    intro h
    exact hx ((map_eq_zero_iff _ (conjugation K L).injective).mp h)
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact mul_ne_zero hx hσx ha.symm
  obtain ⟨n, hn⟩ := hω.base_int a ha0
  obtain ⟨t, ht⟩ := exists_omega_eq_coe ω hx
  refine ⟨n, ?_⟩
  have h2 : ω (x * σ x) = ((t + t : ℝ) : WithTop ℝ) := by
    rw [ω.map_mul, hω.conjugation_eq, ht, WithTop.coe_add]
  rw [← ha, hn, WithTop.coe_eq_coe] at h2
  rw [ht, WithTop.coe_eq_coe]
  linarith

/-- Either all extension values are integral, or a value `1/2` is attained. -/
theorem integral_or_ramified :
    (∀ y : L, y ≠ 0 → ∃ n : ℤ, ω y = ((n : ℝ) : WithTop ℝ)) ∨
      IsRamifiedQuadraticValuation K L ω := by
  by_cases hint : ∀ y : L, y ≠ 0 → ∃ n : ℤ, ω y = ((n : ℝ) : WithTop ℝ)
  · exact Or.inl hint
  right
  push Not at hint
  obtain ⟨x, hx, hxint⟩ := hint
  obtain ⟨n, hn⟩ := hω.exists_half_integer hx
  have hnodd : n % 2 = 1 := by
    by_contra hodd
    have heven : n = 2 * (n / 2) := by omega
    apply hxint (n / 2)
    rw [hn, WithTop.coe_eq_coe]
    have hcast : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) := by exact_mod_cast heven
    linarith
  obtain ⟨π, hπ⟩ := hω.exists_one
  have hπ0 : algebraMap K L π ≠ 0 := by
    intro h0
    rw [h0, ω.map_zero] at hπ
    exact WithTop.top_ne_coe hπ
  refine ⟨hω.conjugation_eq, hω.base_int,
    x * (algebraMap K L π) ^ (-(n / 2)), ?_⟩
  rw [ω.map_mul, hn, omega_zpow ω hπ0 1 hπ, mul_one, ← WithTop.coe_add,
    WithTop.coe_eq_coe]
  have hdecomp : n = 2 * (n / 2) + 1 := by omega
  have hcast : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast hdecomp
  push_cast
  linarith

/-- Every normalized separable quadratic coordinate valuation has an indivisible
central jump, in every field and residue characteristic. -/
theorem hasIndivisibleCentralJump :
    Parameters.HasIndivisibleCentralJump (c := fieldInvolution K L) ω := by
  rcases hω.integral_or_ramified with hint | hram
  · exact exists_indivisible_centralJump_of_integer_values ω hω.conjugation_eq hint
      hω.exists_one
  · exact hram.exists_indivisible_centralJump

end IsNormalizedQuadraticValuation

end Quadratic

end Langlands.GroupScheme.SU3Root
