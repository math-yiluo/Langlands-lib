/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 13 November 2026: extracted the source theorem
LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrank (inventory
M162.016) as the Prop-valued target
Langlands.NYLL.LocalClassFieldTheory.relNorm_maximalIdeal_eq_pow_residue_finrankStatement.
The telescope and the asserted equation are unchanged; the file-level local
instance attribute on FractionRing.liftAlgebra is kept although this statement
does not use it. The source proof and the other declarations are omitted. The
NYLL imports are replaced by Mathlib.RingTheory.Valuation.Extension and
Mathlib.NumberTheory.LocalField.Basic next to the source's two Mathlib imports.
The retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Relative norm of the maximal ideal of a local-field extension: statement target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
lines 321 and 389–403 (inventory M162.016).
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

open scoped ValuativeRel

attribute [local instance] FractionRing.liftAlgebra

/-- In a finite separable local-field extension, the relative ideal norm of
the upstairs maximal ideal is the residue-degree power of the base maximal
ideal. -/
def relNorm_maximalIdeal_eq_pow_residue_finrankStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]] : Prop :=
  Ideal.relNorm 𝒪[K] (𝓂[L] : Ideal 𝒪[L]) =
    (𝓂[K] : Ideal 𝒪[K]) ^ Module.finrank 𝓀[K] 𝓀[L]

end Langlands.NYLL.LocalClassFieldTheory
