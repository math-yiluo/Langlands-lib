/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 294, 2026-11-14: extract the signature of M353.029
as the Prop-valued target d029Statement, move the source-private name to
Langlands.NYLL.PortInternal.M353, and replace the full recursive imports
by the published linear-term and local-field definitions. Source binders
and conclusion are preserved; the proof is reserved for a separate task.
See the paired Markdown and licenses/NYLL/{LICENSE,NOTICE}.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions

/-! # Target for preserving the linear term under a higher-degree monomial -/

universe u v w

namespace Langlands.NYLL.PortInternal.M353

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField
open Langlands.NYLL.LubinTate.SameUniformizer

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

set_option linter.unusedVariables false in
/-- Exact target of source-private M353.029, `hasLinearTerm_add_monomial`. -/
abbrev d029Statement
    {H : MvPowerSeries sigma F.valuationSubring}
    {L : sigma → F.valuationSubring}
    (hH : HasLinearTerm H L)
    (d : sigma →₀ ℕ) (hd : 2 ≤ d.degree)
    (c : F.valuationSubring) : Prop :=
  HasLinearTerm (H + MvPowerSeries.monomial d c) L

end Langlands.NYLL.PortInternal.M353
