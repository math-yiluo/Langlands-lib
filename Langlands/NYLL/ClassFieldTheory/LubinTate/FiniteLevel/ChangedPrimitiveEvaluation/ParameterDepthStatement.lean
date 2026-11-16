/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 322, 2026-11-16: extract the proposition of M393.001
(lines 54–80) from upstream commit fbd320cd8b1b06487c58227e92eb135794267709
as a closed, unproved Prop-valued definition; append Statement to its name,
qualify the namespaces with Langlands.NYLL, rename the term variable u
and its hypothesis hu to a and ha, and replace the imports and module
documentation with the focused statement scope. The original independent
universes, telescope, hypothesis and conclusion are retained.
Disable the unused-variable linter only for this closed target.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.ChangedUniformizer.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.PrincipalUnits.Filtration.Definitions

/-!
# Changed-uniformizer principal-unit depth target

The proposition of NYLL M393.001: a depth-`n+1` unit changes a uniformizer
only in depth `n+2`. This module defines the target for a separate proof.
-/

noncomputable section

universe u v

namespace Langlands.NYLL.LubinTate

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

set_option linter.unusedVariables false in
/-- The target that a depth-`n+1` unit changes a uniformizer only in depth `n+2`. -/
def standardLubinTateChangedUniformizer_sub_mem_maximalIdeal_powStatement : Prop :=
  ∀ {K : Type u} [Field K]
    {F : LocalField.{u, v} K} {π : F.valuationSubring}
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubringˣ) (n : ℕ)
    (ha : a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (n + 1)),
    standardLubinTateChangedUniformizer F π a - π ∈
      F.maximalIdeal ^ (n + 2)

end Langlands.NYLL.LubinTate

end
