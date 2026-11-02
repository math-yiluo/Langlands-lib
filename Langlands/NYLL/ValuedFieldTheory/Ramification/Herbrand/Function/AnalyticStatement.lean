/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.Definitions
import Mathlib.Topology.MetricSpace.Pseudo.Defs

/-!
# Finite Herbrand monotonicity, surjectivity and continuity statement

Statement extraction from NYLL
`Nyll/ValuedFieldTheory/Ramification/Herbrand/Function.lean`,
commit fbd320cd8b1b06487c58227e92eb135794267709,
M303.026–.028 (lines 253–349).
Worker 384 grouped the three theorem signatures into one closed proposition,
retained the source finite-group scope, prefixed the namespace by
`Langlands.NYLL`, and replaced the source imports by the published normalized
definitions and the minimal real metric topology import needed for this target.
No source proof or local subgroup instance is included.
Worker 106 supplied the source analysis and aggregate target design.
The original license and notices are retained in `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

/-- Strict monotonicity, surjectivity and continuity on the full real line
of the normalized Herbrand function of every finite-group filtration. -/
def HerbrandFunctionAnalyticStatement : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] (F : AntitoneNormalSubgroupFiltration G),
    StrictMono (herbrandFunction F) ∧
    Function.Surjective (herbrandFunction F) ∧
    Continuous (herbrandFunction F)

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
