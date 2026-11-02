/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.EvaluationStatement

/-!
# Herbrand evaluation and interpolation proofs

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709,
M303.014–.020 and M303.022–.023 (lines 120–182 and 207–228).
Worker 1199 adapted the nine source proofs to the published definitions,
retained independent comparison universes, proved the value at one without
the source's finite-group instance, and assembled the exact closed target.
The closed right endpoint uses the defining prefix-sum recurrence directly.
Worker 106 supplied the source analysis, proof route and aggregate target design.
The original license and notices are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

universe u v

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G]
variable (F : AntitoneNormalSubgroupFiltration G)

/-- Equal lower-subgroup cardinalities give equal Herbrand functions,
including for groups in independent universes. -/
theorem herbrandFunction_eq_of_card_lower_eq
    {G' : Type v} [Group G']
    (F' : AntitoneNormalSubgroupFiltration G')
    (hcard : ∀ n : ℕ, Nat.card (F.lower n) = Nat.card (F'.lower n))
    (s : ℝ) :
    herbrandFunction F s = herbrandFunction F' s := by
  have hslope : ∀ n : ℕ, herbrandSlope F n = herbrandSlope F' n := by
    intro n
    simp only [herbrandSlope, hcard]
  have hnat : ∀ n : ℕ, herbrandValueNat F n = herbrandValueNat F' n := by
    intro n
    simp only [herbrandValueNat, hslope]
  by_cases hs : 0 ≤ s
  · simp only [herbrandFunction, hs, ↓reduceIte, hnat, hslope]
  · simp only [herbrandFunction, hs, ↓reduceIte]

/-- The Herbrand function is the identity at every nonpositive real. -/
theorem herbrandFunction_of_nonpos {s : ℝ} (hs : s ≤ 0) :
    herbrandFunction F s = s := by
  rcases hs.eq_or_lt with rfl | hs
  · simp [herbrandFunction, herbrandValueNat]
  · simp [herbrandFunction, not_le.mpr hs]

/-- The normalized Herbrand function vanishes at zero. -/
@[simp] theorem herbrandFunction_zero : herbrandFunction F 0 = 0 := by
  exact herbrandFunction_of_nonpos F le_rfl

/-- The normalized Herbrand function fixes minus one. -/
@[simp] theorem herbrandFunction_neg_one : herbrandFunction F (-1) = -1 := by
  exact herbrandFunction_of_nonpos F (by simp)

/-- The affine formula at a specified natural floor. -/
theorem herbrandFunction_of_floor {s : ℝ} (hs : 0 ≤ s) (m : ℕ)
    (hm : Nat.floor s = m) :
    herbrandFunction F s =
      herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m := by
  simp [herbrandFunction, hs, hm]

/-- Evaluation at a natural point is the defining prefix sum. -/
@[simp] theorem herbrandFunction_nat (n : ℕ) :
    herbrandFunction F (n : ℝ) = herbrandValueNat F n := by
  simp [herbrandFunction]

/-- The value at one is the ratio of the first two lower-subgroup
cardinalities, with no finiteness assumption. -/
theorem herbrandFunction_one_eq :
    herbrandFunction F 1 =
      (Nat.card (F.lower 1) : ℝ) / Nat.card (F.lower 0) := by
  rw [show (1 : ℝ) = ((1 : ℕ) : ℝ) by simp, herbrandFunction_nat]
  simp [herbrandValueNat, herbrandSlope]

/-- The defining affine formula on a half-open unit interval. -/
theorem herbrandFunction_eq_on_Ico (m : ℕ) {s : ℝ}
    (hms : (m : ℝ) ≤ s) (hsm : s < (m : ℝ) + 1) :
    herbrandFunction F s =
      herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m := by
  apply herbrandFunction_of_floor F (le_trans (Nat.cast_nonneg m) hms) m
  exact (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg m) hms)).2 ⟨hms, hsm⟩

/-- The affine formula extends to the closed right endpoint by the
prefix-sum recurrence, retaining the slope indexed by `m`. -/
theorem herbrandFunction_eq_on_Icc (m : ℕ) {s : ℝ}
    (hms : (m : ℝ) ≤ s) (hsm : s ≤ (m : ℝ) + 1) :
    herbrandFunction F s =
      herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m := by
  rcases hsm.eq_or_lt with hsm | hsm
  · subst s
    rw [show (m : ℝ) + 1 = ((m + 1 : ℕ) : ℝ) by simp,
      herbrandFunction_nat]
    simp [herbrandValueNat, Finset.sum_range_succ]
  · exact herbrandFunction_eq_on_Ico F m hms hsm

/-- All nine evaluation and interpolation laws, at the exact published
closed target and its two independent universes. -/
theorem herbrandFunctionEvaluation : HerbrandFunctionEvaluationStatement.{u, v} := by
  constructor
  · intro G _ F G' _ F' hcard s
    exact herbrandFunction_eq_of_card_lower_eq F F' hcard s
  · intro G _ F
    exact ⟨(fun s hs => herbrandFunction_of_nonpos F hs),
      herbrandFunction_zero F,
      herbrandFunction_neg_one F,
      (fun s hs m hm => herbrandFunction_of_floor F hs m hm),
      herbrandFunction_nat F,
      herbrandFunction_one_eq F,
      (fun m s hms hsm => herbrandFunction_eq_on_Ico F m hms hsm),
      (fun m s hms hsm => herbrandFunction_eq_on_Icc F m hms hsm)⟩

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
