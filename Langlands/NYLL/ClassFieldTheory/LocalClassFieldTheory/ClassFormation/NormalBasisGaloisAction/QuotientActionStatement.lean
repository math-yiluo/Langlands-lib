/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.GroupTheory.GroupAction.Quotient

/-!
Adapted by Worker 197 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709.
Relation preservation for a stable-subgroup quotient
See the paired Markdown for exact source correspondence and modifications.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe uG uA

def quotientActionOfSubgroupStableStatement
    (G : Type uG) (A : Type uA) [Group G] [CommGroup A]
    [MulDistribMulAction G A] (V : Subgroup A)
    (hstable : ∀ (g : G) (a : A), a ∈ V → g • a ∈ V) : Prop :=
MulAction.QuotientAction G V

end

end Langlands.NYLL.LocalClassFieldTheory
