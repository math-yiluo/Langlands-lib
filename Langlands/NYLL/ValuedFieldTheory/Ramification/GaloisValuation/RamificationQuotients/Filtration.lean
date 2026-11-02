/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Antitone filtrations by normal subgroups

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/GaloisValuation/RamificationQuotients.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, lines 28–44 (M224.001–.002).
Worker 60 extracted the structure and its projection instance, prefixed the namespace
by `Langlands.NYLL`, and reduced the import to Mathlib's subgroup definitions.
The unused universe `v` and `noncomputable section` are omitted.
The fields, binders and instance body are unchanged.
Worker 106 supplied the source extraction and interface analysis.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField

/-- A generic antitone filtration by normal subgroups. This interface contains
only the group-theoretic laws; arithmetic lower ramification filtrations are
canonical values constructed from valued extensions. -/
structure AntitoneNormalSubgroupFiltration (G : Type u) [Group G] where
  /-- The subgroup at each lower-filtration index. -/
  lower : ℕ → Subgroup G
  /-- Every subgroup in the lower filtration is normal. -/
  lower_normal : ∀ n : ℕ, (lower n).Normal
  /-- The lower filtration decreases as its index increases. -/
  antitone : ∀ {m n : ℕ}, m ≤ n → lower n ≤ lower m

namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)

/-- Provides the instance `lower_normal_instance`. -/
instance lower_normal_instance (n : ℕ) : (F.lower n).Normal :=
  F.lower_normal n

end AntitoneNormalSubgroupFiltration

end Langlands.NYLL.RamificationTheory.DiscreteValuationField
