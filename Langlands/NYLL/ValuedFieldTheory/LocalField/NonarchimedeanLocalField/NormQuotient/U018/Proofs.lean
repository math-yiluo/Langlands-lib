/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 31 October 2026:
Extract M093.018 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, import only U018 Statements, and prove the published
closed proposition by introducing its six internal term binders before
the original two-line proof. Omit the source noncomputable section,
unused universe v and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U018.Statements

/-!
# Identity norm classes and extension-unit norms

A base-field unit has identity norm class exactly when it is the norm
of an extension-field unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- A base-field unit has trivial norm class exactly when it lies in the local norm subgroup. -/
theorem normClass_eq_one_iff : NormClassEqOneIffStatement.{u} := by
  intro K L _ _ _ x
  rw [← MonoidHom.mem_range]
  exact QuotientGroup.eq_one_iff x

end Langlands.NYLL.LocalFieldTheory
