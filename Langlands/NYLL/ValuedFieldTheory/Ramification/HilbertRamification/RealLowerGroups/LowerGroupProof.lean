/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with source extraction, six-clause
exact-target, parameter and proof-route analysis contributed by Worker 106:
isolate M304.023–.029 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, import the published target and prerequisite proofs,
retain the six source proofs and normality instance alias, and assemble
the exact closed four-universe conjunction.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.LowerGroupStatement
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.RealIndexProof

/-!
# Elementary real lower ramification laws: proof

The six laws and the normality instance alias M304.023–.029 of the pinned
NYLL `RealLowerGroups.lean`, assembled as the exact published closed target.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

open Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF

section Properties

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- States the theorem `mem_lowerRamificationGroup_iff`. -/
@[simp] theorem mem_lowerRamificationGroup_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) (σ : Gal(L/K)) :
    σ ∈ lowerRamificationGroup
        (base := base) (target := target) huniq s ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          realRamificationIdeal target s :=
  Iff.rfl

/-- At an integral index, the real definition is exactly the usual
`m^(n+1)` displacement condition. -/
theorem mem_lowerRamificationGroup_nat_iff
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (n : ℕ) (σ : Gal(L/K)) :
    σ ∈ lowerRamificationGroup
        (base := base) (target := target) huniq (n : ℝ) ↔
      ∀ a : target.valuationSubring,
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          target.maximalIdeal ^ (n + 1) := by
  simp only [mem_lowerRamificationGroup_iff, realRamificationIdeal_nat]

/-- The real lower-ramification definition: the lower groups are decreasing in their real index. -/
theorem lowerRamificationGroup_antitone
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    Antitone (lowerRamificationGroup
      (base := base) (target := target) huniq) := by
  intro s t hst σ hσ a
  exact realRamificationIdeal_antitone (target := target) hst (hσ a)

/-- The real lower-ramification definition: every real lower ramification group is normal. -/
theorem lowerRamificationGroup_normal
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) :
    (lowerRamificationGroup
      (base := base) (target := target) huniq s).Normal := by
  refine Subgroup.Normal.mk ?_
  intro σ hσ τ a
  let b := valuationSubringAutOfUniqueExtension
    (base := base) (target := target) huniq τ⁻¹ a
  have hb :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ b - b ∈
        realRamificationIdeal target s :=
    hσ b
  have hmap :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b) ∈
        realRamificationIdeal target s :=
    (valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
      (base := base) (target := target) huniq τ s _).2 hb
  have hrewrite :
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (τ * σ * τ⁻¹) a - a =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq τ
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b) := by
    simp [b, map_sub]
  rwa [hrewrite]

/-- Provides the instance `instNormal`. -/
instance lowerRamificationGroup.instNormal
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) :
    (lowerRamificationGroup
      (base := base) (target := target) huniq s).Normal :=
  lowerRamificationGroup_normal
    (base := base) (target := target) huniq s

/-- The real lower-ramification definition: `G_{-1}` is the full Galois group. -/
@[simp] theorem lowerRamificationGroup_neg_one
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target) :
    lowerRamificationGroup
      (base := base) (target := target) huniq (-1) = ⊤ := by
  ext σ
  simp [mem_lowerRamificationGroup_iff]

/-- The all-real extension is constant at the full Galois group below the
distinguished endpoint `-1`. -/
theorem lowerRamificationGroup_eq_top_of_le_neg_one
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    {s : ℝ} (hs : s ≤ -1) :
    lowerRamificationGroup
      (base := base) (target := target) huniq s = ⊤ := by
  ext σ
  simp [mem_lowerRamificationGroup_iff,
    realRamificationIdeal_eq_top_of_le_neg_one (target := target) hs]

end Properties

/-- The complete closed real lower-ramification group property target. -/
theorem lowerRamificationGroupProperties :
    LowerRamificationGroupPropertiesStatement.{u, v, w, x} := by
  intro K L _ _ _ base target _ huniq
  exact ⟨mem_lowerRamificationGroup_iff (base := base) (target := target) huniq,
    mem_lowerRamificationGroup_nat_iff (base := base) (target := target) huniq,
    lowerRamificationGroup_antitone (base := base) (target := target) huniq,
    lowerRamificationGroup_normal (base := base) (target := target) huniq,
    lowerRamificationGroup_neg_one (base := base) (target := target) huniq,
    lowerRamificationGroup_eq_top_of_le_neg_one (base := base) (target := target) huniq⟩

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
