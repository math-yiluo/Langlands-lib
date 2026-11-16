/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 205, 2026-11-16: extract M267.003, lines 73–79,
from Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace
with Langlands.NYLL and prove the focused closed proposition target,
introducing its unchanged Type-0 source telescope. Retain the source rfl proof and simp attribute.
Worker 562, 2026-11-16: reuse the proof-only shared draft and verify it
against the published target; clarify its paired proof documentation.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison.U003.Statements

/-! # NYLL M267.003: canonical comparison proof -/

namespace Langlands.NYLL.LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- The comparison map sends a norm class to the corresponding unramified valuation class. -/
@[simp]
theorem normQuotientToUnramifiedNormQuotient_mk :
    normQuotientToUnramifiedNormQuotient_mkStatement := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x
  rfl

end Langlands.NYLL.LocalClassFieldTheory
