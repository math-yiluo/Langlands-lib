/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract only the proof of M093.029 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed
NormClassEqOneOfMemStatement by introducing its seven internal binders.
Retain the original reverse implication of normClass_eq_one_iff_mem,
the sole universe u, implicit representative x and explicit witness hx.
Import only U029.Statements and preserve its entire public chain.
Omit the source noncomputable section, unused universe v and other units.
Install no instance or simp registration.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U029.Statements

/-!
# Norm-image membership gives trivial norm class

Proof that a representative in the actual unit-norm image maps to the
identity under the canonical norm-quotient projection.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- A representative from the local norm subgroup has trivial norm class. -/
theorem normClass_eq_one_of_mem : NormClassEqOneOfMemStatement.{u} := by
  intro K L _ _ _ x hx
  exact (normClass_eq_one_iff_mem K L x).2 hx

end Langlands.NYLL.LocalFieldTheory
