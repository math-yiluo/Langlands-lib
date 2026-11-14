/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 331, 2026-11-14: extract M353.001 as the exact Prop-valued Statement target,
prefix namespaces with Langlands.NYLL, and reuse focused published LocalField
and LinearTerm imports. Omit the proof and unrelated source units.
See the paired Markdown. Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Definitions

/-! # Target for the linear term of the prescribed linear form -/

noncomputable section

universe u v w

namespace Langlands.NYLL.LubinTate.SameUniformizer

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K}
variable {sigma : Type w} [Fintype sigma]

/-- The prescribed linear form itself has the prescribed linear term. -/
def linearForm_hasLinearTermStatement
    (L : sigma → F.valuationSubring) : Prop :=
  HasLinearTerm (linearForm L) L

end Langlands.NYLL.LubinTate.SameUniformizer

end
