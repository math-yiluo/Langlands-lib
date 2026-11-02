/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1045, 2026-11-02, with source extraction, grouping and
target design contributed by Worker 106: extract the signatures of
M303.005–.012 from upstream commit fbd320cd8b1b06487c58227e92eb135794267709
and conjoin them as one closed Prop target in two blocks, the first without and
the second with the source `[Finite G]`; prefix the namespace with
Langlands.NYLL and reuse the published Herbrand definitions. The proofs,
docstrings, `@[simp]` attribute, local subgroup instances and noncomputable
section are omitted. Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.Definitions

/-!
# Elementary slope and natural-sum laws of the Herbrand function: statement

This closed proposition conjoins the signatures of M303.005–.012 (lines 55–109)
of `Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

/-- For every antitone normal subgroup filtration, the natural Herbrand sum
vanishes at `0` and adds the slope `herbrandSlope F n` from `n` to `n + 1`; for
a finite group, every slope is positive, nonnegative and at least
`1 / |F.lower 0|`, the natural sum at `n` is nonnegative and at least
`n / |F.lower 0|`, and the natural sum is strictly monotone. -/
def HerbrandDiscreteElementaryStatement : Prop :=
  (∀ {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G),
    herbrandValueNat F 0 = 0 ∧
    ∀ n : ℕ, herbrandValueNat F (n + 1) = herbrandValueNat F n + herbrandSlope F n) ∧
  (∀ {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G),
    (∀ i : ℕ, 0 < herbrandSlope F i) ∧
    (∀ i : ℕ, 0 ≤ herbrandSlope F i) ∧
    (∀ i : ℕ, (1 : ℝ) / Nat.card (F.lower 0) ≤ herbrandSlope F i) ∧
    (∀ n : ℕ, 0 ≤ herbrandValueNat F n) ∧
    (∀ n : ℕ, (n : ℝ) / Nat.card (F.lower 0) ≤ herbrandValueNat F n) ∧
    StrictMono (herbrandValueNat F))

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
