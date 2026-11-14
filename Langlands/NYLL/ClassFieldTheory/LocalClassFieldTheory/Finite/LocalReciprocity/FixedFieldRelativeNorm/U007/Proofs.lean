/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 56, 13 November 2026:
Extract only the proof of M276.007
relativeCosetAction_abstractFixedFieldUnit_val from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
FixedFieldRelativeNorm.lean at fbd320cd8b1b06487c58227e92eb135794267709,
under the source name with the Langlands.NYLL prefix, proving the published
statement. Introduce the statement's binders and keep the source tactic
proof unchanged.
Worker 605, 14 November 2026: reuse Worker 56's shared proof draft
for Task 6334 and check it against the current Library base; retain the
proof and original attribution unchanged.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.FixedFieldRelativeNorm.U004.Statements

/-!
# The coset action on a fixed unit is evaluation of an embedding: proof
-/

namespace Langlands.NYLL.LocalClassFieldTheory

/-- States the theorem `relativeCosetAction_abstractFixedFieldUnit_val`. -/
theorem relativeCosetAction_abstractFixedFieldUnit_val :
    relativeCosetAction_abstractFixedFieldUnit_valStatement := by
  intro k Ω _ _ _ _ K L hLK x q
  refine Quotient.inductionOn' q ?_
  intro σ
  rfl

end Langlands.NYLL.LocalClassFieldTheory
