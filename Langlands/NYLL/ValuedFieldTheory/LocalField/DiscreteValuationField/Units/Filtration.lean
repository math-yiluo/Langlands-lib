/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Antitone subgroup filtration data

Adapted by Worker 321 from NYLL M120.001–002 at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. Modifications: add the
`Langlands.NYLL` namespace prefix and isolate these data declarations.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

open scoped BigOperators

namespace DiscreteValuationField

/-- A generic antitone filtration by subgroups of a group.  No valued-field
semantics are asserted by this interface alone. -/
structure AntitoneSubgroupFiltration (G : Type u) [Group G] where
  /-- The subgroup at each natural-number filtration level. -/
  subgroup : ℕ → Subgroup G
  /-- Higher filtration levels are contained in lower ones. -/
  antitone : ∀ {m n : ℕ}, m ≤ n → subgroup n ≤ subgroup m

namespace AntitoneSubgroupFiltration

variable {G : Type u} [Group G] (U : AntitoneSubgroupFiltration G)

/-- The `n`-th principal-unit subgroup. -/
def principalUnitSubgroup (n : ℕ) : Subgroup G :=
  U.subgroup n


end AntitoneSubgroupFiltration

end DiscreteValuationField

end Langlands.NYLL.LocalFieldTheory
