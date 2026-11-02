/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.Definitions

/-!
# Finite basic Herbrand statement

Statement extraction from NYLL
`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709,
M303.021 and M303.024–.025 (lines 184–205 and 230–251).
Worker 60 grouped the three theorem signatures as one closed proposition,
prefixed the namespace by `Langlands.NYLL`, and imported the published
normalized definitions unchanged. All three clauses retain `[Finite G]`.
No source proof or local subgroup instance is included.
Worker 106 supplied the source analysis and aggregate target design.
The original license and notices are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

open scoped BigOperators

/-- The first-value bounds, closed-interval cardinal-sum formula and
nonnegativity law, in that order, for every finite-group filtration. -/
def HerbrandFiniteBasicStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G),
    (0 < herbrandFunction F 1 ∧ herbrandFunction F 1 ≤ 1) ∧
    (∀ (m : ℕ) {s : ℝ}, (m : ℝ) ≤ s → s ≤ (m : ℝ) + 1 →
      herbrandFunction F s =
        ((∑ i ∈ Finset.range m, (Nat.card (F.lower (i + 1)) : ℝ)) +
          (s - (m : ℝ)) * (Nat.card (F.lower (m + 1)) : ℝ)) /
          (Nat.card (F.lower 0) : ℝ)) ∧
    (∀ {s : ℝ}, 0 ≤ s → 0 ≤ herbrandFunction F s)

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
