import Langlands.Shimura.Unitary.LocalDivisionLevels
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Published division levels in a uniformizer coordinate -/

noncomputable section
universe u v

namespace Langlands.Shimura.LocalDivision
open Langlands.CentralDivision

variable (k : Type u) (D : Type v)
variable [NontriviallyNormedField k] [CompleteSpace k] [IsUltrametricDist k]
variable [LocallyCompactSpace k] [DivisionRing D] [Algebra k D] [FiniteDimensional k D]
variable [TopologicalSpace D] [IsModuleTopology k D]
variable (uniformizer : Dˣ) (hsmall : regularAbsoluteValue k D (uniformizer : D) < 1)
variable (N : ℕ) (hN : 0 < N)

/-- The published congruence level at the radius of the chosen uniformizer power. -/
def uniformizerLevel : CompactOpenLevel Dˣ :=
  congruenceLevel k D (regularAbsoluteValue k D (uniformizer : D) ^ N)
    (pow_pos ((regularAbsoluteValue k D).pos_iff.mpr uniformizer.ne_zero) N)
    (pow_lt_one₀ ((regularAbsoluteValue k D).nonneg _) hsmall hN.ne')

/-- The norm level is exactly `1 + uniformizer^N O_D` inside ambient units. -/
theorem mem_uniformizerLevel_iff (g : Dˣ) :
    g ∈ (uniformizerLevel k D uniformizer hsmall N hN).subgroup ↔
      ∃ x ∈ integerRing k D, (g : D) = 1 + (uniformizer : D) ^ N * x := by
  change regularAbsoluteValue k D ((g : D) - 1) ≤
    regularAbsoluteValue k D (uniformizer : D) ^ N ↔ _
  constructor
  · intro hg
    let x := ((uniformizer : D) ^ N)⁻¹ * ((g : D) - 1)
    have hx : (uniformizer : D) ^ N * x = (g : D) - 1 := by
      dsimp only [x]
      rw [← mul_assoc, mul_inv_cancel₀ (pow_ne_zero N uniformizer.ne_zero), one_mul]
    refine ⟨x, ?_, by rw [hx, add_sub_cancel]⟩
    change regularAbsoluteValue k D x ≤ 1
    have hpos := pow_pos ((regularAbsoluteValue k D).pos_iff.mpr uniformizer.ne_zero) N
    apply (mul_le_mul_iff_right₀ hpos).mp
    have hv := congrArg (regularAbsoluteValue k D) hx
    rw [map_mul, map_pow] at hv
    rw [hv, mul_one]
    exact hg
  · rintro ⟨x, hx, hg⟩
    change regularAbsoluteValue k D x ≤ 1 at hx
    rw [hg, add_sub_cancel_left, map_mul, map_pow]
    exact mul_le_of_le_one_right (pow_nonneg ((regularAbsoluteValue k D).nonneg _) _) hx

theorem uniformizerLevel_le_maximalCompactLevel :
    (uniformizerLevel k D uniformizer hsmall N hN).subgroup ≤
      (maximalCompactLevel k D).subgroup :=
  congruenceLevel_le_maximalCompactLevel k D _ _ _

/-- The congruence subgroup is invariant under conjugation by all division-algebra units. -/
instance uniformizerLevel_normal :
    (uniformizerLevel k D uniformizer hsmall N hN).subgroup.Normal where
  conj_mem g hg a := by
    change regularAbsoluteValue k D ((g : D) - 1) ≤
      regularAbsoluteValue k D (uniformizer : D) ^ N at hg
    change regularAbsoluteValue k D (((a : D) * (g : D) * (↑a⁻¹ : D)) - 1) ≤ _
    have h : (a : D) * (g : D) * (↑a⁻¹ : D) - 1 =
        (a : D) * ((g : D) - 1) * (↑a⁻¹ : D) := by
      rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
    rw [h, map_mul, map_mul]
    have ha : regularAbsoluteValue k D (a : D) * regularAbsoluteValue k D (↑a⁻¹ : D) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    calc
      regularAbsoluteValue k D (a : D) * regularAbsoluteValue k D ((g : D) - 1) *
          regularAbsoluteValue k D (↑a⁻¹ : D) =
        regularAbsoluteValue k D ((g : D) - 1) *
          (regularAbsoluteValue k D (a : D) * regularAbsoluteValue k D (↑a⁻¹ : D)) := by
        ac_rfl
      _ ≤ _ := by rw [ha, mul_one]; exact hg

/-- The finite quotient of the integral unit group at the given division level. -/
abbrev UniformizerLevelQuotient :=
  (maximalCompactLevel k D).subgroup ⧸
    (uniformizerLevel k D uniformizer hsmall N hN).subgroup.subgroupOf
      (maximalCompactLevel k D).subgroup

theorem finite_uniformizerLevelQuotient :
    Finite (UniformizerLevelQuotient k D uniformizer hsmall N hN) := by
  let : IsTopologicalRing D := IsModuleTopology.isTopologicalRing k D
  let K := (maximalCompactLevel k D).subgroup
  let U := (uniformizerLevel k D uniformizer hsmall N hN).subgroup
  have : CompactSpace K := isCompact_iff_compactSpace.mp (maximalCompactLevel k D).isCompact
  exact Subgroup.quotient_finite_of_isOpen (U.subgroupOf K)
    (Subgroup.subgroupOf_isOpen K U (uniformizerLevel k D uniformizer hsmall N hN).openSubgroup.isOpen)

/-- Replacing the chosen unit by its d-th power multiplies the level index by d. -/
theorem uniformizerLevel_pow_subgroup (d : ℕ) (hd : 0 < d)
    (hsmallPow : regularAbsoluteValue k D ((uniformizer ^ d : Dˣ) : D) < 1) :
    (uniformizerLevel k D (uniformizer ^ d) hsmallPow N hN).subgroup =
      (uniformizerLevel k D uniformizer hsmall (d * N) (Nat.mul_pos hd hN)).subgroup := by
  apply Subgroup.ext
  intro g
  change regularAbsoluteValue k D ((g : D) - 1) ≤
      regularAbsoluteValue k D ((uniformizer ^ d : Dˣ) : D) ^ N ↔
    regularAbsoluteValue k D ((g : D) - 1) ≤
      regularAbsoluteValue k D (uniformizer : D) ^ (d * N)
  rw [Units.val_pow_eq_pow_val, map_pow, pow_mul]

end Langlands.Shimura.LocalDivision
