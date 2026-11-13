/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 152, 13 November 2026:
Extract the proof of M266.017 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean
(lines 179–183) at fbd320cd8b1b06487c58227e92eb135794267709. Add the
Langlands.NYLL namespace prefix and prove the published closed statement by
introducing its seven internal binders. Replace the source's rewrite by
M266.016 and M266.012 with Mathlib's QuotientGroup.eq_one_iff applied to the
published quotient projection M266.013. Import only the published
QuotientStatements target. Omit all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.QuotientStatements

/-!
# Trivial unramified norm classes

A field unit has the identity unramified norm class exactly when it lies in
the unramified norm subgroup.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

universe u

/-- A unit has trivial norm class exactly when it belongs to the unramified norm subgroup. -/
theorem unramifiedNormClass_eq_one_iff_mem :
    unramifiedNormClass_eq_one_iff_memStatement.{u} := by
  intro K _ _ _ _ n x
  exact QuotientGroup.eq_one_iff (N := unramifiedNormSubgroup K n) x

end Langlands.NYLL.LocalClassFieldTheory
