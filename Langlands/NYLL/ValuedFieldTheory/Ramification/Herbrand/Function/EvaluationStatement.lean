/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.Definitions

/-!
# Herbrand evaluation and interpolation statement

Statement extraction from NYLL
`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709,
M303.014–.020 and M303.022–.023 (lines 120–182 and 207–228).
Worker 1199 packaged the nine source laws as one closed proposition,
prefixed the namespace by `Langlands.NYLL`, and imported the published
normalized definitions unchanged. The two comparison groups retain
independent universes. No finite-group instance or source proof is included.
Worker 106 supplied the source analysis and aggregate target design.
The original license and notices are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

universe u v

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

/-- The cardinality comparison law, followed by the eight elementary
evaluation and unit-interval interpolation laws, for arbitrary filtrations. -/
def HerbrandFunctionEvaluationStatement : Prop :=
  (∀ {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G)
      {G' : Type v} [Group G'] (F' : AntitoneNormalSubgroupFiltration G')
      (_hcard : ∀ n : ℕ, Nat.card (F.lower n) = Nat.card (F'.lower n))
      (s : ℝ),
      herbrandFunction F s = herbrandFunction F' s) ∧
  (∀ {G : Type u} [Group G] (F : AntitoneNormalSubgroupFiltration G),
    (∀ (s : ℝ), s ≤ 0 → herbrandFunction F s = s) ∧
    herbrandFunction F 0 = 0 ∧
    herbrandFunction F (-1) = -1 ∧
    (∀ (s : ℝ), 0 ≤ s → ∀ (m : ℕ), Nat.floor s = m →
      herbrandFunction F s =
        herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m) ∧
    (∀ (n : ℕ), herbrandFunction F (n : ℝ) = herbrandValueNat F n) ∧
    herbrandFunction F 1 =
      (Nat.card (F.lower 1) : ℝ) / Nat.card (F.lower 0) ∧
    (∀ (m : ℕ) (s : ℝ), (m : ℝ) ≤ s → s < (m : ℝ) + 1 →
      herbrandFunction F s =
        herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m) ∧
    (∀ (m : ℕ) (s : ℝ), (m : ℝ) ≤ s → s ≤ (m : ℝ) + 1 →
      herbrandFunction F s =
        herbrandValueNat F m + (s - (m : ℝ)) * herbrandSlope F m))

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
