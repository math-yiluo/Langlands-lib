/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-02, with source/interface extraction,
reuse analysis and closed-target design contributed by Worker 106:
extract the signatures of M303.030-.034/.036-.037 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709 into one closed Prop-valued
definition, retain the finite-group scope, prefix the namespace with
Langlands.NYLL, and use the published normalized function and chosen inverse.
Replace upstream imports by the inverse-definition module and real topology.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.InverseDefinition
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Finite inverse Herbrand laws statement

The seven source theorem signatures are grouped in their original order.
The group, its finiteness instance, the filtration and every real variable
are universally quantified within this proposition.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

/-- The two inverse identities, strict monotonicity, surjectivity, continuity
and preservation of `[-1, ∞)` for every finite-group Herbrand function. -/
def HerbrandInverseLawsStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G),
    (∀ t : ℝ, herbrandFunction F (inverseHerbrandFunction F t) = t) ∧
    (∀ s : ℝ, inverseHerbrandFunction F (herbrandFunction F s) = s) ∧
    StrictMono (inverseHerbrandFunction F) ∧
    Function.Surjective (inverseHerbrandFunction F) ∧
    Continuous (inverseHerbrandFunction F) ∧
    (∀ s : ℝ, herbrandFunction F s ∈ Set.Ici (-1) ↔ s ∈ Set.Ici (-1)) ∧
    (∀ t : ℝ, inverseHerbrandFunction F t ∈ Set.Ici (-1) ↔ t ∈ Set.Ici (-1))

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
