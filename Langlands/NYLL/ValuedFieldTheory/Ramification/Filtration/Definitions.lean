/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Group.Subgroup.Lattice
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Natural-ceiling subgroup step filtration

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/Filtration.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709, definition at lines 29–31.
Worker 22 extracted this definition, prefixed the namespace by `Langlands.NYLL`,
and made the universe explicit. The imports and defining expression are unchanged.
The upstream license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

noncomputable section

namespace Langlands.NYLL.RamificationTheory

universe u

/-- Extend an arbitrary natural-indexed subgroup family to the real line by
its natural-number ceiling. No monotonicity of the family is required. -/
def natCeilStepFiltration {G : Type u} [Group G]
    (F : ℕ → Subgroup G) (t : ℝ) : Subgroup G :=
  F (Nat.ceil t)

end Langlands.NYLL.RamificationTheory
