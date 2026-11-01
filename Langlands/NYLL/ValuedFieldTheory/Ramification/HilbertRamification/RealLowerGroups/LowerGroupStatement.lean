/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with source extraction, six-clause
grouping and exact parameter analysis contributed by Worker 106:
extract the conclusions of M304.023–.029 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 into one closed Prop target.
Prefix namespaces with Langlands.NYLL, reuse the published actual lower
subgroup and its underlying objects, and move all mathematical binders
inside the Prop. Retain four independent universes and comparison universe x.
Omit the proofs and the redundant normality instance alias.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.LowerGroup

/-!
# Elementary real lower ramification laws: statement

This closed proposition groups the six mathematical conclusions of
M304.023–.029, lines 370–469 of the pinned NYLL `RealLowerGroups.lean`.
M304.027 repeats the normality conclusion as an instance alias.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- For every supplied unique valuation extension, the genuine real lower groups
have the stated real and natural displacement carriers, are antitone and normal,
and equal the full Galois group at and below `-1`. -/
def LowerRamificationGroupPropertiesStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target),
    (∀ (s : ℝ) (σ : Gal(L/K)),
      σ ∈ lowerRamificationGroup
          (base := base) (target := target) huniq s ↔
        ∀ a : target.valuationSubring,
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a ∈
            realRamificationIdeal target s) ∧
    (∀ (n : ℕ) (σ : Gal(L/K)),
      σ ∈ lowerRamificationGroup
          (base := base) (target := target) huniq (n : ℝ) ↔
        ∀ a : target.valuationSubring,
          valuationSubringAutOfUniqueExtension
              (base := base) (target := target) huniq σ a - a ∈
            target.maximalIdeal ^ (n + 1)) ∧
    Antitone (lowerRamificationGroup
      (base := base) (target := target) huniq) ∧
    (∀ s : ℝ,
      (lowerRamificationGroup
        (base := base) (target := target) huniq s).Normal) ∧
    (lowerRamificationGroup
      (base := base) (target := target) huniq (-1) = ⊤) ∧
    (∀ {s : ℝ}, s ≤ -1 →
      lowerRamificationGroup
        (base := base) (target := target) huniq s = ⊤)

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
