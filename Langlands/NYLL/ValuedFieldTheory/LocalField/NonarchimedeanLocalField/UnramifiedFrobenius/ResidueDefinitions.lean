/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 3, 2026-11-13: extract only M264.001, the definition
residueExtensionArithmeticFrobeniusOfValuationExtension at lines 33–44 of
upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace
with Langlands.NYLL; replace the source imports by three Mathlib modules; write
the body as a term instead of a tactic block and drop its redundant local
`Algebra.IsAlgebraic` declaration, which instance search supplies; rewrite the
doc comment. The parameters, result type and the Frobenius automorphism are
otherwise unchanged. The retained license and notices are in
licenses/NYLL/.
-/

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Extension

/-!
# Residue arithmetic Frobenius of a valuation extension

This module adapts only M264.001, lines 33–44 of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/UnramifiedFrobenius.lean`.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u

open scoped ValuativeRel

/-- Arithmetic Frobenius of the actual residue-field extension supplied by a
valuation extension: Mathlib's finite-field Frobenius `x ↦ x ^ #𝓀[K]`,
as a `𝓀[K]`-algebra automorphism of `𝓀[L]`. -/
def residueExtensionArithmeticFrobeniusOfValuationExtension
    (K L : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L]
    [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)] :
    𝓀[L] ≃ₐ[𝓀[K]] 𝓀[L] :=
  letI := Fintype.ofFinite 𝓀[K]
  FiniteField.frobeniusAlgEquivOfAlgebraic 𝓀[K] 𝓀[L]

end

end Langlands.NYLL.LocalFieldTheory
