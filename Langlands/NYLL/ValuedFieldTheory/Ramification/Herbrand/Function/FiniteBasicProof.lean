/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.FiniteBasicStatement
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.EvaluationProof
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite basic Herbrand proofs

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709,
M303.021 and M303.024–.025 (lines 184–205 and 230–251).
Worker 60 adapted the bounds proof to the published evaluation laws,
proved the cardinal-sum identity by distributing the common denominator,
and proved nonnegativity termwise at the natural floor.
Worker 106 supplied the source analysis, direct proof route and task design.
The namespace is prefixed by `Langlands.NYLL`; imports use the unchanged
published target and evaluation proof. All three helpers retain `Finite G`.
No additional subgroup instance or discrete elementary proof is used.
The original license and notices are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

open scoped BigOperators

section FiniteGroup

variable {G : Type u} [Group G] [Finite G]
variable (F : AntitoneNormalSubgroupFiltration G)


/-- The first Herbrand value is strictly positive and at most one. -/
theorem herbrandFunction_one_pos_le_one :
    0 < herbrandFunction F 1 ∧ herbrandFunction F 1 ≤ 1 := by
  have hden : (0 : ℝ) < Nat.card (F.lower 0) := Nat.cast_pos.mpr Nat.card_pos
  have hnum : (0 : ℝ) < Nat.card (F.lower 1) := Nat.cast_pos.mpr Nat.card_pos
  have hsub : F.lower 1 ≤ F.lower 0 := F.antitone (Nat.zero_le 1)
  let incl : F.lower 1 → F.lower 0 := fun x => ⟨x.1, hsub x.2⟩
  have hincl : Function.Injective incl := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : F.lower 0 => (z : G)) h)
  have hcard : Nat.card (F.lower 1) ≤ Nat.card (F.lower 0) :=
    Nat.card_le_card_of_injective incl hincl
  rw [herbrandFunction_one_eq]
  constructor
  · exact div_pos hnum hden
  · apply (div_le_iff₀ hden).2
    simpa using (Nat.cast_le.mpr hcard :
      (Nat.card (F.lower 1) : ℝ) ≤ Nat.card (F.lower 0))

/-- The actual lower-subgroup cardinal-sum formula on each closed unit interval. -/
theorem herbrandFunction_eq_card_sum_of_mem_Icc
    {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G)
    (m : ℕ) {s : ℝ}
    (hms : (m : ℝ) ≤ s) (hsm : s ≤ (m : ℝ) + 1) :
    herbrandFunction F s =
      ((∑ i ∈ Finset.range m, (Nat.card (F.lower (i + 1)) : ℝ)) +
        (s - (m : ℝ)) * (Nat.card (F.lower (m + 1)) : ℝ)) /
        (Nat.card (F.lower 0) : ℝ) := by
  rw [herbrandFunction_eq_on_Icc F m hms hsm]
  simp_rw [herbrandValueNat, herbrandSlope, div_eq_mul_inv]
  rw [← Finset.sum_mul, add_mul, mul_assoc]

/-- The finite-group Herbrand function is nonnegative at every nonnegative real. -/
theorem herbrandFunction_nonneg {s : ℝ} (hs : 0 ≤ s) :
    0 ≤ herbrandFunction F s := by
  rw [herbrandFunction_eq_card_sum_of_mem_Icc F (Nat.floor s)
    (Nat.floor_le hs) (Nat.lt_floor_add_one s).le]
  exact div_nonneg
    (add_nonneg (Finset.sum_nonneg (fun i _ => Nat.cast_nonneg _))
      (mul_nonneg (sub_nonneg.mpr (Nat.floor_le hs)) (Nat.cast_nonneg _)))
    (Nat.cast_nonneg _)

end FiniteGroup

/-- The three finite basic laws at the exact published closed target. -/
theorem herbrandFiniteBasic : HerbrandFiniteBasicStatement.{u} := by
  intro G _ _ F
  exact ⟨herbrandFunction_one_pos_le_one F,
    (fun m {s} hms hsm => herbrandFunction_eq_card_sum_of_mem_Icc F m hms hsm),
    (fun {s} hs => herbrandFunction_nonneg F hs)⟩

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
