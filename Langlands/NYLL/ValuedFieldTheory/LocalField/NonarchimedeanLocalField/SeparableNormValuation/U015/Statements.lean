/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 13 November 2026: extracted the source theorem
LocalClassFieldTheory.fractionRing_integerRing_isSeparable (inventory M162.015)
as the Prop-valued target
Langlands.NYLL.LocalClassFieldTheory.fractionRing_integerRing_isSeparableStatement.
The telescope, the file-level local instance attribute on
FractionRing.liftAlgebra and the asserted type are unchanged. The source proof
and the other declarations are omitted. The NYLL imports are replaced by
Mathlib.RingTheory.Valuation.Extension and
Mathlib.Topology.Algebra.Valued.ValuativeRel next to the source's two Mathlib
imports. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Valuation.Extension
import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!
# Separability of the fraction fields of valuation integer rings: statement target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
lines 321 and 371–380 (inventory M162.015).
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

open scoped ValuativeRel

attribute [local instance] FractionRing.liftAlgebra

/-- Separability of an actual field extension transfers to the canonical
fraction fields of its valuation integer rings. -/
def fractionRing_integerRing_isSeparableStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K]
    [Field L] [ValuativeRel L]
    [Algebra K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)] : Prop :=
  Algebra.IsSeparable (FractionRing 𝒪[K]) (FractionRing 𝒪[L])

end Langlands.NYLL.LocalClassFieldTheory
