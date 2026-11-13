/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 13 November 2026: extracted the source theorem
LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparable
(inventory M162.019) as the Prop-valued target
Langlands.NYLL.LocalClassFieldTheory.v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement.
The telescope and the asserted equation are unchanged; the file-level local
instance attribute on FractionRing.liftAlgebra is kept although this statement
does not use it. The source's v and normUnits are the published
Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.v (M128.001) and
Langlands.NYLL.LocalFieldTheory.normUnits (M092.002). The source proof and the
other declarations are omitted. The NYLL imports are replaced by the two
published modules defining v and normUnits and by
Mathlib.RingTheory.Valuation.Extension next to the source's two Mathlib
imports. The retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions

/-!
# Normalized valuation of a separable field norm: statement target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
lines 321 and 492–508 (inventory M162.019).
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

/-- Finite local reciprocity, normalized norm calculation for every finite separable
local-field extension: the normalized value of a field norm is the actual
residue degree times the upstairs normalized value. -/
def v_normUnits_eq_residue_finrank_mul_of_isSeparableStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    (x : Lˣ) : Prop :=
  v K (Additive.ofMul (normUnits K L x)) =
    (Module.finrank 𝓀[K] 𝓀[L] : Int) *
      v L (Additive.ofMul x)

end Langlands.NYLL.LocalClassFieldTheory
