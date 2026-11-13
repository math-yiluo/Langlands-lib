/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 13 November 2026: extracted the source theorems
LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparable
(inventory M162.017) and
LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparable
(inventory M162.018) as the Prop-valued targets
Langlands.NYLL.LocalClassFieldTheory.v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement
and
Langlands.NYLL.LocalClassFieldTheory.v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement.
The telescopes and the asserted equations are unchanged; the file-level local
instance attribute on FractionRing.liftAlgebra is kept although these
statements do not use it. The source's v, normUnits,
integerRingUniformizerFieldUnit and inverseIntegerRingUniformizerFieldUnit are
the published Langlands.NYLL adaptations (M128.001, M092.002, M133.007,
M133.009). The source proofs and the other declarations are omitted. The NYLL
imports are replaced by the published modules defining these four names and by
Mathlib.RingTheory.Valuation.Extension next to the source's two Mathlib
imports. The retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Mathlib.FieldTheory.SeparableClosure
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.Valuation.Extension
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U007.Definitions

/-!
# Normalized valuation of the norm of a prime element: statement targets

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/SeparableNormValuation.lean`,
line 321 and lines 412–427 (inventory M162.017) and 473–487 (inventory M162.018).
-/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

open scoped ValuativeRel
open Langlands.NYLL.LocalFieldTheory
open Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField

attribute [local instance] FractionRing.liftAlgebra

/-- The norm of the chosen upstairs prime element has base normalized value
the negative of the actual residue degree, for every finite separable
extension (not only a Galois one). -/
def v_normUnits_integerRingUniformizerFieldUnit_of_isSeparableStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] : Prop :=
  v K (Additive.ofMul
      (normUnits K L (integerRingUniformizerFieldUnit L))) =
    -(Module.finrank 𝓀[K] 𝓀[L] : Int)

/-- The norm of the positive generator (the inverse chosen prime element) has
base normalized value equal to the actual residue degree. -/
def v_normUnits_inverseIntegerRingUniformizerFieldUnit_of_isSeparableStatement
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    [IsIntegralClosure 𝒪[L] 𝒪[K] L] : Prop :=
  v K (Additive.ofMul
      (normUnits K L (inverseIntegerRingUniformizerFieldUnit L))) =
    (Module.finrank 𝓀[K] 𝓀[L] : Int)

end Langlands.NYLL.LocalClassFieldTheory
