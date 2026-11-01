/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/- Modifications by Worker 384 and Worker 106 (2026-11-01): extract the
   statements of M248.003 `localCompleteDVF_integerRing_isIntegralClosure`
   and M248.004 `localCompleteDVF_integerRing_moduleFinite` from upstream
   commit fbd320cd8b1b06487c58227e92eb135794267709, omit their proofs, and
   group their conclusions in one closed Prop-valued definition with their
   full shared telescope and independent universes u and v. Prefix the
   namespace with Langlands.NYLL, expand the source integer-ring notation
   to the actual canonical valuation subrings, qualify Valuation.HasExtension
   with _root_, and use the published canonical module and focused Mathlib
   imports. The original LICENSE and NOTICE are retained in licenses/NYLL/. -/

import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Defs
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical

/-!
# Canonical integer rings in finite separable local extensions

The closed statement that the actual upstairs valuation subring is the
integral closure of the actual base valuation subring and is finite over it,
using the supplied extension of the canonical valuations.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- The canonical valuation subring of a finite separable local extension
is the integral closure of the base valuation subring and a finite module
over it, with scalars induced by the supplied valuation extension. -/
def LocalCompleteDVFIntegerRingPropertiesStatement : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [_root_.Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)],
    IsIntegralClosure (ValuativeRel.valuation L).valuationSubring
      (ValuativeRel.valuation K).valuationSubring L ∧
    Module.Finite (ValuativeRel.valuation K).valuationSubring
      (ValuativeRel.valuation L).valuationSubring

end Langlands.NYLL.LocalFieldTheory
