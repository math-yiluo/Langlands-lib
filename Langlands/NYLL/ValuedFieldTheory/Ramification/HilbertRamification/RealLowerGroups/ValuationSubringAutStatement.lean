/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 785, 2026-11-01, with source extraction, grouping and
parameter analysis contributed by Worker 106: extract the signatures of
M304.015–.021 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709
and conjoin them as one closed Prop target; prefix namespaces with
Langlands.NYLL, reuse the published automorphism, uniqueness predicate and
real-index ideal, and move all mathematical binders inside the Prop.
Preserve all four independent universes and comparison universe x. The proofs
are omitted. Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.ValuationSubringAut
import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.RealIndex

/-!
# Valuation-ring automorphism laws and preservation properties: statement

This closed proposition conjoins the signatures of M304.015–.021, lines 184–303 of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- The valuation-ring automorphism induced by a supplied field automorphism under
unique extension evaluates as that automorphism in `L`, sends the identity to the
identity, is multiplicative in the automorphism, is inverted by the inverse
automorphism, and preserves membership in the maximal ideal, in each of its natural
powers and in each real-index ideal. -/
def ValuationSubringAutPropertiesStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{u, v} K}
    {target : Langlands.NYLL.ValuationTheory.DiscreteValuationField.DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq :
      Langlands.NYLL.RamificationTheory.DiscreteValuationField.DVF.HasUniqueValuationExtension.{u, v, w, x, x}
        base target),
    (∀ (σ : Gal(L/K)) (a : target.valuationSubring),
      ((valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ a :
          target.valuationSubring) : L) = σ (a : L)) ∧
    (∀ a : target.valuationSubring,
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq 1 a = a) ∧
    (∀ (σ τ : Gal(L/K)) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq (σ * τ) a =
        valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ
          (valuationSubringAutOfUniqueExtension
            (base := base) (target := target) huniq τ a)) ∧
    (∀ (σ : Gal(L/K)) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
        (base := base) (target := target) huniq σ
        (valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ⁻¹ a) = a) ∧
    (∀ (σ : Gal(L/K)) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ↔
        a ∈ target.maximalIdeal) ∧
    (∀ (σ : Gal(L/K)) (n : ℕ) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a ∈ target.maximalIdeal ^ n ↔
        a ∈ target.maximalIdeal ^ n) ∧
    (∀ (σ : Gal(L/K)) (s : ℝ) (a : target.valuationSubring),
      valuationSubringAutOfUniqueExtension
          (base := base) (target := target) huniq σ a ∈
            realRamificationIdeal target s ↔
        a ∈ realRamificationIdeal target s)

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
