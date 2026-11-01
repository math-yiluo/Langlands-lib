/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract the proof of M093.022 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only U022 Statements. Prove its published
closed proposition by introducing all six internal term binders before
the original rewrite by normClass_mem_ker_iff K L x and reflexivity.
Preserve the shared universe u. Omit the source noncomputable section,
unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U022.Statements

/-!
# A norm class is one exactly on the norm image

Triviality of a canonical norm class is equivalent to membership of its
representative in the actual norm image subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- A norm class is one exactly when its representative is a local norm. -/
theorem normClass_eq_one_iff_mem : NormClassEqOneIffMemStatement.{u} := by
  intro K L _ _ _ x
  rw [← normClass_mem_ker_iff K L x]
  rfl

end Langlands.NYLL.LocalFieldTheory
