/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with source extraction, exact carrier,
parameter and subgroup proof-route analysis contributed by Worker 106:
isolate M304.022 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, import the published actual automorphism and its laws,
and retain the original subgroup carrier and three structure proofs.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAutProof
import Mathlib.Tactic.Ring

/-!
# The genuine real lower ramification subgroup

This isolates M304.022, lines 304–368 of the pinned NYLL
`RealLowerGroups.lean`, on the actual chosen target valuation ring.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

open Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF

variable {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
variable {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
variable {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
variable [base.valuation.HasExtension target.valuation]

/-- The real lower-ramification definition: the real-index lower ramification
group.  On the natural range `s >= -1`, membership is exactly the condition that
all integral displacements have normalized additive value at least `s + 1`,
expressed intrinsically as membership in `m ^ ceil(s + 1)`. -/
def lowerRamificationGroup
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x}
      base target)
    (s : ℝ) : Subgroup Gal(L/K) where
  carrier :=
    {σ | ∀ a : target.valuationSubring,
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a - a ∈
        realRamificationIdeal target s}
  one_mem' := by
    intro a
    rw [valuationSubringAutOfUniqueExtension_one_apply, sub_self]
    exact Ideal.zero_mem _
  mul_mem' := by
    intro σ τ hσ hτ a
    have hτa :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq τ a - a ∈
          realRamificationIdeal target s :=
      hτ a
    have hmapτa :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq τ a - a) ∈
          realRamificationIdeal target s :=
      (valuationSubringAutOfUniqueExtension_mem_realRamificationIdeal_iff
        (base := base) (target := target) huniq σ s _).2 hτa
    have hσa :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a ∈
          realRamificationIdeal target s :=
      hσ a
    have hdecomp :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq (σ * τ) a - a =
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ
              (valuationSubringAutOfUniqueExtension
                (base := base) (target := target) huniq τ a - a) +
            (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a) := by
      rw [valuationSubringAutOfUniqueExtension_mul_apply, map_sub]
      ring
    rw [hdecomp]
    exact Ideal.add_mem _ hmapτa hσa
  inv_mem' := by
    intro σ hσ a
    let b := valuationSubringAutOfUniqueExtension
      (base := base) (target := target) huniq σ⁻¹ a
    have hb :
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ b - b ∈
          realRamificationIdeal target s :=
      hσ b
    have hab : a - b ∈ realRamificationIdeal target s := by
      simpa [b] using hb
    have hba : b - a ∈ realRamificationIdeal target s := by
      simpa [sub_eq_add_neg, add_comm] using
        (realRamificationIdeal target s).neg_mem hab
    simpa [b] using hba

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
