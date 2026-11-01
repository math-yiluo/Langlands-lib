/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 31 October 2026:
Extract the proof of M093.017 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing
its six internal binders, then following the original proof unchanged.
Import only U017 Statements. Omit the source noncomputable section and
all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U017.Statements

/-!
# Norm classes of extension-unit norms

The norm of every extension-field unit has the identity class in the
norm quotient.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The quotient class of any extension-unit norm is the identity norm class. -/
theorem mk_normUnits_eq_one : MkNormUnitsEqOneStatement.{u} := by
  intro K L _ _ _ x
  exact (QuotientGroup.eq_one_iff (normUnits K L x)).2 ⟨x, rfl⟩

end Langlands.NYLL.LocalFieldTheory
