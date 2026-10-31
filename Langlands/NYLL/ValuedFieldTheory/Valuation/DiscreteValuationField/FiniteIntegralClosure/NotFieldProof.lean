/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 764 (2026-10-30): adapt the proof of M245.010
(FiniteIntegralClosure.lean, lines 307-327) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 to its published closed target,
with independent universe parameters u, v, w and the Langlands.NYLL prefix;
expand base.valuationSubring to the actual valuation subring. Prove the
injectivity of the scalar map into the integral closure inline, instead of
through the M245.001 and M245.002 wrappers and a faithful scalar action,
and pass it directly to the current Mathlib lemma
isField_of_isIntegral_of_isField. Replace upstream imports by the published
target and focused Mathlib imports. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.DVRStatements
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.SimpleRing.Basic
import Mathlib.RingTheory.Valuation.Discrete.Basic

/-!
# The integral closure over a complete DVF is not a field

The only theorem proves NYLL M245.010 as its exact published closed
proposition.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- The actual integral closure of the valuation subring of a complete DVF in a
separable extension is not a field (M245.010). Neither finite dimensionality
nor nontriviality of the extension is assumed. -/
theorem integralClosure_not_isField_of_finite_separable.{u, v, w} :
    IntegralClosureNotIsFieldOfFiniteSeparableStatement.{u, v, w} := by
  intro K L _ _ _ base _ hB
  let A := base.valuation.valuationSubring
  let B := integralClosure A L
  have hinj : Function.Injective (algebraMap A B) := by
    intro x y hxy
    apply Subtype.ext
    apply (algebraMap K L).injective
    exact congrArg (fun z : B => (z : L)) hxy
  exact IsDiscreteValuationRing.not_isField A (isField_of_isIntegral_of_isField hinj hB)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
