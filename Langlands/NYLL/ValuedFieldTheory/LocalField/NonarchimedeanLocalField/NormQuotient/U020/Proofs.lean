/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract M093.020 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only U020 Statements, and prove the published
closed proposition by introducing its five internal term binders before
the original quotient-kernel proof. Omit the source noncomputable
section, unused universe v and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U020.Statements

/-!
# Kernel of the norm-class homomorphism

The kernel of the canonical homomorphism to norm classes is the actual
norm image subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The kernel of the norm-class homomorphism is the local norm subgroup. -/
theorem normClass_ker : NormClassKerStatement.{u} := by
  intro K L _ _ _
  let N := localNormSubgroup K L
  exact QuotientGroup.ker_mk' (N := N)

end Langlands.NYLL.LocalFieldTheory
