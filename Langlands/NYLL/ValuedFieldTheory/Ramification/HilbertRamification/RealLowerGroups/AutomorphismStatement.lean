/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-01, with formulation contributed by Worker 106:
extract the signature of M304.003 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as a closed Prop target; prefix
namespaces with Langlands.NYLL, move all mathematical binders inside the Prop,
and import the published uniqueness predicate with focused Mathlib support.
Preserve all four independent universes and comparison universe x. The proof
is omitted. Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.HilbertRamification.RealLowerGroups.UniqueExtension
import Mathlib.Algebra.Algebra.Equiv

/-!
# Valuation-ring preservation from unique extension: statement

This closed proposition adapts the signature of M304.003, lines 70–77 of
`Nyll/ValuedFieldTheory/Ramification/HilbertRamification/RealLowerGroups.lean`.
The extension relation and uniqueness are hypotheses; valuation-ring
preservation is the conclusion.
-/

universe u v w x

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField

open Langlands.NYLL.ValuationTheory.DiscreteValuationField

namespace DVF

-- Retain the source's explicit uniqueness-hypothesis name in the Prop telescope.
set_option linter.unusedVariables false in
/-- Unique extension forces every supplied algebra automorphism to preserve
membership in the chosen target valuation subring. -/
def MemValuationSubringAlgEquivIffOfHasUniqueValuationExtensionStatement : Prop :=
  ∀ {K : Type u} {L : Type w} [Field K] [Field L] [Algebra K L]
    {base : DVF.{u, v} K} {target : DVF.{w, x} L}
    [base.valuation.HasExtension target.valuation]
    (huniq : HasUniqueValuationExtension.{u, v, w, x, x} base target)
    (σ : L ≃ₐ[K] L) (z : L),
    z ∈ target.valuation.valuationSubring ↔
      σ z ∈ target.valuation.valuationSubring

end DVF

end Langlands.NYLL.RamificationTheory.DiscreteValuationField
