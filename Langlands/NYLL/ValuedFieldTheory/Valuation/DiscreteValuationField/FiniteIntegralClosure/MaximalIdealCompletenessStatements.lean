/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 384 (2026-10-30): extract only the statements of
M105.013 (AdicPower.lean, lines 247-253, ambient context lines 22-24) and
M245.014 (FiniteIntegralClosure.lean, lines 428-457, ambient context lines
23 and 30-31) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 as two closed Prop definitions.
Quantify all mathematical parameters inside their bodies with independent
universe levels; prefix the namespaces with Langlands.NYLL and rename the
targets. Expand base.valuationSubring to base.valuation.valuationSubring,
reuse the published CanonicalIntegralClosure.maximalIdeal, and replace the
source imports by its published module and Mathlib's adic completeness
definitions. The grouped layout follows the direct source dependency of
M245.014 on M105.013. No theorem proofs or global instances are included.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.FiniteIntegralClosure.MaximalIdeal
import Mathlib.RingTheory.AdicCompletion.Basic

/-!
# Positive-power and integral-closure maximal-ideal completeness targets

The two closed propositions state NYLL M105.013 and M245.014. All mathematical
parameters are quantified inside the propositions. These are statement
targets without proofs.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField

/-- Completeness of a module for a positive power of an ideal implies its
completeness for the same ideal. This is the M105.013 proposition target,
not a proof. -/
def IsAdicCompleteOfIsAdicCompletePowStatement.{u, v} : Prop :=
  ∀ (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]
    (I : Ideal R) {n : ℕ} (hn : 0 < n) [IsAdicComplete (I ^ n) M],
    IsAdicComplete I M

end Langlands.NYLL.ValuationTheory.DiscreteValuationField

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- In a finite separable extension of a field with a supplied complete discrete
valuation, the actual integral closure of its valuation subring is complete
for its own canonical maximal ideal. This is the M245.014 proposition target,
not a proof. -/
def IntegralClosureMaximalIdealIsAdicCompleteOfFiniteSeparableStatement.{u, v, w} : Prop :=
  ∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
    IsAdicComplete
      (CanonicalIntegralClosure.maximalIdeal (K := K) (L := L) base)
      (integralClosure base.valuation.valuationSubring L)

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
