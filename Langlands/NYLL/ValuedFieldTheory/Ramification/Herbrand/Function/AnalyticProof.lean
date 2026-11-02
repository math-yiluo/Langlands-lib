/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.AnalyticStatement
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.EvaluationProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.FiniteBasicProof
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.DiscreteElementaryProof
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite Herbrand monotonicity, surjectivity and continuity proofs

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709,
M303.026–.028 (lines 253–349).
Worker 1237 adapted the three source proofs to the published evaluation,
finite-basic and discrete elementary helpers, and assembled the exact closed
target `HerbrandFunctionAnalyticStatement`.
The namespace is prefixed by `Langlands.NYLL`; the source local subgroup
instances and noncomputable section are omitted. All three laws retain the
source ambient `Finite G`.
Worker 106 supplied the source analysis, proof route and task design.
The original license and notices are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

section FiniteGroup

variable {G : Type u} [Group G] [Finite G]
variable (F : AntitoneNormalSubgroupFiltration G)

/-- The Herbrand function is strictly increasing, as asserted after
the Herbrand quotient theorem. -/
theorem herbrandFunction_strictMono : StrictMono (herbrandFunction F) := by
  intro s t hst
  by_cases ht : t ≤ 0
  · rw [herbrandFunction_of_nonpos F (le_trans hst.le ht),
      herbrandFunction_of_nonpos F ht]
    exact hst
  by_cases hs : s < 0
  · rw [herbrandFunction_of_nonpos F hs.le]
    exact lt_of_lt_of_le hs (herbrandFunction_nonneg F (le_of_not_ge ht))
  have hs0 : 0 ≤ s := le_of_not_gt hs
  have ht0 : 0 ≤ t := hs0.trans hst.le
  set m := ⌊s⌋₊
  set n := ⌊t⌋₊
  have hmle : (m : ℝ) ≤ s := Nat.floor_le hs0
  have hmlt : s < m + 1 := Nat.lt_floor_add_one s
  have hnle : (n : ℝ) ≤ t := Nat.floor_le ht0
  have hnlt : t < n + 1 := Nat.lt_floor_add_one t
  have hmn : m ≤ n := Nat.floor_mono hst.le
  rw [herbrandFunction_eq_on_Ico F m hmle hmlt,
    herbrandFunction_eq_on_Ico F n hnle hnlt]
  rcases hmn.eq_or_lt with hmn | hmn
  · rw [← hmn]
    nlinarith [herbrandSlope_pos F m]
  · have hs_upper :
        herbrandValueNat F m + (s - m) * herbrandSlope F m <
          herbrandValueNat F (m + 1) := by
      rw [herbrandValueNat_succ F]
      nlinarith [herbrandSlope_pos F m]
    have hnat : herbrandValueNat F (m + 1) ≤ herbrandValueNat F n :=
      (herbrandValueNat_strictMono F).monotone (by omega)
    have ht_lower : herbrandValueNat F n ≤
        herbrandValueNat F n + (t - n) * herbrandSlope F n :=
      le_add_of_nonneg_right
        (mul_nonneg (sub_nonneg.mpr hnle) (herbrandSlope_nonneg F n))
    exact hs_upper.trans_le (hnat.trans ht_lower)

/-- Every real number is a value of the Herbrand function. -/
theorem herbrandFunction_surjective : Function.Surjective (herbrandFunction F) := by
  intro y
  by_cases hy : y ≤ 0
  · exact ⟨y, herbrandFunction_of_nonpos F hy⟩
  set d : ℝ := (Nat.card (F.lower 0) : ℝ) with hd_def
  have hd : 0 < d := by
    rw [hd_def]
    exact_mod_cast (show 0 < Nat.card (F.lower 0) from Finite.card_pos)
  obtain ⟨N, hN⟩ := exists_nat_gt (y * d)
  have hyN : y ≤ herbrandValueNat F N := by
    apply le_trans ?_ (nat_div_card_le_herbrandValueNat F N)
    rw [← hd_def]
    exact (le_div_iff₀ hd).2 hN.le
  have hex : ∃ n : ℕ, y ≤ herbrandValueNat F n := ⟨N, hyN⟩
  set n := Nat.find hex
  have hn_upper : y ≤ herbrandValueNat F n := Nat.find_spec hex
  have hn_pos : 0 < n := by
    by_contra hn
    have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
    rw [hn0, herbrandValueNat_zero F] at hn_upper
    exact hy hn_upper
  set m := n - 1
  have hn_eq : n = m + 1 := by omega
  have hm_lt_n : m < n := by omega
  have hm_lower : herbrandValueNat F m < y :=
    lt_of_not_ge (Nat.find_min hex hm_lt_n)
  set x : ℝ := m + (y - herbrandValueNat F m) / herbrandSlope F m with hx_def
  have hx_lower : (m : ℝ) ≤ x :=
    le_add_of_nonneg_right
      (div_nonneg (sub_nonneg.mpr hm_lower.le) (herbrandSlope_nonneg F m))
  have hx_upper : x ≤ m + 1 := by
    have hyadd : y ≤ herbrandValueNat F m + herbrandSlope F m := by
      rw [← herbrandValueNat_succ F, ← hn_eq]
      exact hn_upper
    have hfrac : (y - herbrandValueNat F m) / herbrandSlope F m ≤ 1 :=
      (div_le_one (herbrandSlope_pos F m)).2 (by linarith)
    rw [hx_def]
    linarith
  refine ⟨x, ?_⟩
  rw [herbrandFunction_eq_on_Icc F m hx_lower hx_upper, hx_def]
  field_simp [(herbrandSlope_pos F m).ne']
  ring

/-- Continuity of the piecewise-linear Herbrand function, from monotonicity
and surjectivity. -/
theorem continuous_herbrandFunction : Continuous (herbrandFunction F) :=
  (herbrandFunction_strictMono F).monotone.continuous_of_surjective
    (herbrandFunction_surjective F)

end FiniteGroup

/-- The three analytic laws M303.026–.028 at the exact published closed
target. -/
theorem herbrandFunctionAnalytic : HerbrandFunctionAnalyticStatement.{u} := by
  intro G _ _ F
  exact ⟨herbrandFunction_strictMono F, herbrandFunction_surjective F,
    continuous_herbrandFunction F⟩

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
