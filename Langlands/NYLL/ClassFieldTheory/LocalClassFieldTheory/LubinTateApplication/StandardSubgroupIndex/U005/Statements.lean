/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 332, 13 November 2026, from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709:
extract only the signature of M377.005 (StandardSubgroupIndex.lean:124–128),
add the Langlands.NYLL namespace prefix and Statement suffix, and quantify
its complete telescope inside a Prop-valued definition. Make Type*'s universe
explicit as u. Retain only Mathlib.GroupTheory.Index; omit the proof and the
unrelated local-field context. See Statements.md and licenses/NYLL/.
-/

import Mathlib.GroupTheory.Index

universe u

namespace Langlands.NYLL.LubinTate

/-- A finite-index subgroup contained in a subgroup of equal index is equal to it. -/
def subgroup_eq_of_le_of_index_eq_of_ne_zeroStatement : Prop :=
  ∀ {G : Type u} [Group G] {H N : Subgroup G},
    H ≤ N → H.index = N.index → H.index ≠ 0 → H = N

end Langlands.NYLL.LubinTate
