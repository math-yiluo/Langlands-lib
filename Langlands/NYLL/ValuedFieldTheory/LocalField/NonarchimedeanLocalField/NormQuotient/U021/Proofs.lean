/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1153, 1 November 2026:
Extract M093.021 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only U021 Statements. Prove its published
closed proposition by introducing all six internal term binders before
the original rewrite by normClass_ker K L. Preserve the shared universe u.
Omit the source noncomputable section, unused universe v and other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U021.Statements

/-!
# Membership in the norm-class kernel

Membership in the canonical norm-class kernel is equivalent to membership
in the actual norm image subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Membership in the kernel of the norm-class map is equivalent to membership in the local norm
subgroup. -/
theorem normClass_mem_ker_iff : NormClassMemKerIffStatement.{u} := by
  intro K L _ _ _ x
  rw [normClass_ker K L]

end Langlands.NYLL.LocalFieldTheory
