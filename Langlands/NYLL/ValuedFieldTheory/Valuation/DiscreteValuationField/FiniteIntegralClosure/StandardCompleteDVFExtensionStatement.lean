/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modifications by Worker 384 (2026-10-31): select only the existence,
HasExtension and actual IsIntegralClosure consequence of M245.018,
exists_integralClosure_standard_fundamental_identity, from upstream
commit fbd320cd8b1b06487c58227e92eb135794267709,
FiniteIntegralClosure.lean lines 631-685, with ambient context at lines
23 and 30-31. Omit the fundamental-identity conjunct and all proofs.
Replace the selected theorem consequence by a closed Prop definition,
internalize all mathematical parameters, retain independent u/v/w and
the same CompleteDVF.{w,0} witness, prefix the namespace with
Langlands.NYLL, and rename the target. Expand the CompleteDVF
valuationSubring abbreviations and qualify Mathlib's HasExtension.
Replace the source imports by the published CompleteDVF module and
focused Mathlib imports. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Valuation.DiscreteValuationField.Complete.Definitions
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
import Mathlib.RingTheory.Valuation.Extension

/-!
# Complete-DVF extension with its actual integral closure

This closed proposition selects the existence consequence of NYLL M245.018.
One complete-DVF target extends the supplied base valuation and has the
actual integral closure as its valuation subring. Its value group lies in
`Type 0`; the field and base value-group universes remain independent.
This module defines the statement without proving it.
-/

namespace Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension

/-- Every supplied finite separable algebra over a complete DVF admits one
complete-DVF extension whose actual valuation subring is the integral
closure, with the canonical scalar structures induced by its extension
witness. This is the existence consequence of M245.018, without its
fundamental-identity conjunct or a proof. -/
def ExistsIntegralClosureStandardCompleteDVFExtensionStatement.{u, v, w} : Prop :=
  ∀ (K : Type u) (L : Type w) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (base : CompleteDVF.{u, v} K) [Algebra.IsSeparable K L],
    ∃ target : CompleteDVF.{w, 0} L,
      ∃ hExt : _root_.Valuation.HasExtension base.valuation target.valuation,
        letI : _root_.Valuation.HasExtension base.valuation target.valuation := hExt
        IsIntegralClosure target.valuation.valuationSubring
          base.valuation.valuationSubring L

end Langlands.NYLL.ValuationTheory.DiscreteValuationField.ValuedExtension
