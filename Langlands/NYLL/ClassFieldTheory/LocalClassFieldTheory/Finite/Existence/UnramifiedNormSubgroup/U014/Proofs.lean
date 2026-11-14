/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 562, 2026-11-14: extract M266.014 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and prove the published closed Statement target by introducing
its original parameters. Retain the source proof term and import only the
published quotient statements and their dependencies.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.QuotientStatements

/-!
# Surjectivity of the unramified norm class projection

This module adapts M266.014, source lines 156–159 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- Every unramified norm class is represented by a field unit. -/
theorem unramifiedNormClass_surjective :
    unramifiedNormClass_surjectiveStatement.{u} := by
  intro K _ _ _ _ n
  exact QuotientGroup.mk'_surjective (unramifiedNormSubgroup K n)

end Langlands.NYLL.LocalClassFieldTheory
