/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.InverseStatement
import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.AnalyticProof
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Finite inverse Herbrand laws proofs

Adapted from NYLL `Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709,
M303.030–.034 and M303.036–.037 (lines 355–408).
Worker 1237 adapted the seven source proofs to the published inverse
definition, analytic proof and evaluation proof, and assembled the exact
closed target `HerbrandInverseLawsStatement`.
The namespace is prefixed by `Langlands.NYLL`; the source local subgroup
instances, noncomputable section and the intervening order isomorphism
M303.035 are omitted. All seven laws retain the source ambient `Finite G`.
Worker 106 supplied the source analysis, proof route and task design.
The original license and notices are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

section FiniteGroup

variable {G : Type u} [Group G] [Finite G]
variable (F : AntitoneNormalSubgroupFiltration G)

/-- States the theorem `herbrandFunction_inverseHerbrandFunction`. -/
@[simp] theorem herbrandFunction_inverseHerbrandFunction (t : ℝ) :
    herbrandFunction F (inverseHerbrandFunction F t) = t :=
  Function.rightInverse_invFun (herbrandFunction_surjective F) t

/-- States the theorem `inverseHerbrandFunction_herbrandFunction`. -/
@[simp] theorem inverseHerbrandFunction_herbrandFunction (s : ℝ) :
    inverseHerbrandFunction F (herbrandFunction F s) = s :=
  Function.leftInverse_invFun (herbrandFunction_strictMono F).injective s

/-- States the theorem `inverseHerbrandFunction_strictMono`. -/
theorem inverseHerbrandFunction_strictMono : StrictMono (inverseHerbrandFunction F) := by
  intro s t hst
  apply (herbrandFunction_strictMono F).lt_iff_lt.mp
  simpa using hst

/-- States the theorem `inverseHerbrandFunction_surjective`. -/
theorem inverseHerbrandFunction_surjective :
    Function.Surjective (inverseHerbrandFunction F) := by
  intro s
  exact ⟨herbrandFunction F s, inverseHerbrandFunction_herbrandFunction F s⟩

/-- States the theorem `continuous_inverseHerbrandFunction`. -/
theorem continuous_inverseHerbrandFunction : Continuous (inverseHerbrandFunction F) :=
  (inverseHerbrandFunction_strictMono F).monotone.continuous_of_surjective
    (inverseHerbrandFunction_surjective F)

/-- States the theorem `herbrandFunction_mem_Ici_neg_one_iff`. -/
theorem herbrandFunction_mem_Ici_neg_one_iff {s : ℝ} :
    herbrandFunction F s ∈ Set.Ici (-1) ↔ s ∈ Set.Ici (-1) := by
  change -1 ≤ herbrandFunction F s ↔ -1 ≤ s
  simpa only [herbrandFunction_neg_one F] using
    ((herbrandFunction_strictMono F).le_iff_le :
      herbrandFunction F (-1) ≤ herbrandFunction F s ↔ (-1 : ℝ) ≤ s)

/-- States the theorem `inverseHerbrandFunction_mem_Ici_neg_one_iff`. -/
theorem inverseHerbrandFunction_mem_Ici_neg_one_iff {t : ℝ} :
    inverseHerbrandFunction F t ∈ Set.Ici (-1) ↔ t ∈ Set.Ici (-1) := by
  change -1 ≤ inverseHerbrandFunction F t ↔ -1 ≤ t
  have hψ : inverseHerbrandFunction F (-1) = -1 := by
    simpa only [herbrandFunction_neg_one F] using
      inverseHerbrandFunction_herbrandFunction F (-1)
  simpa only [hψ] using
    ((inverseHerbrandFunction_strictMono F).le_iff_le :
      inverseHerbrandFunction F (-1) ≤ inverseHerbrandFunction F t ↔ (-1 : ℝ) ≤ t)

end FiniteGroup

/-- The seven inverse laws M303.030–.034 and M303.036–.037 at the exact
published closed target. -/
theorem herbrandInverseLaws : HerbrandInverseLawsStatement.{u} := by
  intro G _ _ F
  exact ⟨herbrandFunction_inverseHerbrandFunction F,
    inverseHerbrandFunction_herbrandFunction F,
    inverseHerbrandFunction_strictMono F,
    inverseHerbrandFunction_surjective F,
    continuous_inverseHerbrandFunction F,
    fun _ => herbrandFunction_mem_Ici_neg_one_iff F,
    fun _ => inverseHerbrandFunction_mem_Ici_neg_one_iff F⟩

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
