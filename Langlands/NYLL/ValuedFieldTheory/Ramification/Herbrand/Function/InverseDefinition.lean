/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 1199, 2026-11-02, with source/interface extraction and
reuse analysis contributed by Worker 106:
isolate M303.029 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix namespaces with
Langlands.NYLL, and import the published normalized function and Mathlib
Function.invFun. Omit the unused finite-group assumption, local subgroup
instances and analytic/inverse theorems; retain the definition body.
Retained license and notices: licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.Ramification.Herbrand.Function.Definitions
import Mathlib.Logic.Function.Basic

/-!
# The inverse Herbrand function as data

This extracts M303.029 of the pinned NYLL `Herbrand/Function.lean`.
Its definition uses `Function.invFun` for every supplied filtration;
inverse laws have separate hypotheses and are not part of this module.
-/

universe u

namespace Langlands.NYLL.RamificationTheory.DiscreteValuationField
namespace AntitoneNormalSubgroupFiltration

variable {G : Type u} [Group G]
variable (F : AntitoneNormalSubgroupFiltration G)

/-- The inverse Herbrand function `ψ`. -/
noncomputable def inverseHerbrandFunction (t : ℝ) : ℝ :=
  Function.invFun (herbrandFunction F) t

end AntitoneNormalSubgroupFiltration
end Langlands.NYLL.RamificationTheory.DiscreteValuationField
