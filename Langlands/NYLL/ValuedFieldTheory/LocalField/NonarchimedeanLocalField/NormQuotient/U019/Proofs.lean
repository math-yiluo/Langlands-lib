/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract M093.019 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only U019 Statements, and prove the published
closed proposition by introducing its seven internal term binders before
the original quotient equality proof. Omit the source noncomputable
section, unused universe v and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U019.Statements

/-!
# Equality of norm classes

Two base-field units have equal norm classes exactly when their quotient
belongs to the actual norm image subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Two units have the same norm class exactly when their quotient is a local norm. -/
theorem normClass_eq_iff_div_mem : NormClassEqIffDivMemStatement.{u} := by
  intro K L _ _ _ x y
  let N := localNormSubgroup K L
  exact QuotientGroup.eq_iff_div_mem (N := N)

end Langlands.NYLL.LocalFieldTheory
