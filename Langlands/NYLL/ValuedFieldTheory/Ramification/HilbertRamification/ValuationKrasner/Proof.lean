/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 578, 2026-11-14: extract the proof of M397.001 from
commit fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, and prove the exact published closed proposition using
focused statement and additive-valuation-invariance imports.
Retained license and notices: licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.ValuationKrasner.Statements
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RamificationDepth.ActionProof

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- The valuation-theoretic Krasner stabilizer step under unique extension. -/
theorem valuationSubringAutOfUniqueExtension_eq_of_fixed_of_close :
    valuationSubringAutOfUniqueExtension_eq_of_fixed_of_closeStatement.{u, v, w, x} := by
  intro K L _ _ _ base target _ huniq σ a b hfix hclose
  by_contra hne
  have hfirst :
      IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - b) =
        IsDiscreteValuationRing.addVal target.valuationSubring
          (a - b) := by
    calc
      IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - b) =
        IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ (a - b)) := by
              apply congrArg
                (IsDiscreteValuationRing.addVal
                  target.valuationSubring)
              rw [map_sub, hfix]
      _ = IsDiscreteValuationRing.addVal target.valuationSubring
          (a - b) :=
        addVal_valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ (a - b)
  have hsecond :
      IsDiscreteValuationRing.addVal target.valuationSubring (b - a) =
        IsDiscreteValuationRing.addVal target.valuationSubring (a - b) := by
    have hneg : b - a = -(a - b) := by ring
    rw [hneg,
      (IsDiscreteValuationRing.addVal target.valuationSubring).map_neg]
  have hultra :=
    IsDiscreteValuationRing.addVal_add
      (R := target.valuationSubring)
      (a :=
        valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - b)
      (b := b - a)
  have hle :
      IsDiscreteValuationRing.addVal target.valuationSubring (a - b) ≤
        IsDiscreteValuationRing.addVal target.valuationSubring
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq σ a - a) := by
    have hsum :
        (valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - b) +
            (b - a) =
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a := by
      ring
    simpa [hfirst, hsecond, hsum] using hultra
  exact (not_le_of_gt (hclose hne)) hle

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
