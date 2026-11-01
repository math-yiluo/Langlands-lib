/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1160, 31 October 2026:
Extract the proof of M093.016 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing
its eight internal binders, then following the original proof unchanged.
Keep the protected theorem name. Import only U016 Statements. Omit the
source noncomputable section and all other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U016.Statements

/-!
# Induction on norm-quotient classes

A property of norm-quotient classes holds for every class once it holds
for the norm class of every base-field unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Eliminate a norm-quotient class through the canonical quotient map,
without exposing the quotient representation to clients. -/
protected theorem NormQuotient.inductionOn :
    NormQuotientInductionOnStatement.{u} := by
  intro K L _ _ _ motive q h
  change motive (show Kˣ ⧸ localNormSubgroup K L from q)
  refine QuotientGroup.induction_on q ?_
  intro x
  exact h x

end Langlands.NYLL.LocalFieldTheory
