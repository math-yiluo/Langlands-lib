/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 384 (2026-10-31): extract only the statement of
M245.017, exists_integralClosure_standard_completeDVF, from upstream
commit fbd320cd8b1b06487c58227e92eb135794267709,
FiniteIntegralClosure.lean lines 513-629, with ambient context at lines
23 and 30-31. Replace the theorem by a closed Prop-valued definition,
quantify every mathematical parameter inside its body, prefix the
namespace with Langlands.NYLL, and rename the target. Expand both
CompleteDVF.valuationSubring abbreviations to valuation.valuationSubring;
retain the pointwise membership iff and the same Type 0-valued target
in both conjuncts. Replace the source imports by the public CompleteDVF
module and focused Mathlib imports. No proof or other source declaration
is included. The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
# Actual integral-closure complete-DVF existence target

This closed proposition states NYLL M245.017 for arbitrary independent field,
base value-group and extension universes. The same complete-DVF witness has
exactly the actual integral closure as its valuation subring, expressed by
pointwise membership, and a ring equivalence with that integral closure.
This module defines the statement without proving it.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- A finite separable extension of a supplied complete DVF admits a complete
DVF with value group in `Type 0` whose valuation subring is pointwise the
actual integral closure and is ring-equivalent to it. This is the M245.017
proposition target, not a proof. -/
def ExistsIntegralClosureStandardCompleteDVFStatement.{u, v, w} : Prop :=
  ∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
    ∃ target : CompleteDVF.{w, 0} L,
      (∀ z : L,
        z ∈ target.valuation.valuationSubring ↔
          z ∈ (integralClosure base.valuation.valuationSubring L).toSubring) ∧
      ∃ _ : (integralClosure base.valuation.valuationSubring L) ≃+*
        target.valuation.valuationSubring, True

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
