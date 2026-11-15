/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions

/-!
# The condition that a Herbrand quotient is defined

Modified by Worker 5264, 15 November 2026: port the source definition
M119.001 `CyclicCohomology.ProfiniteCohomology.Herbrand.HerbrandQuotientDefined`
of `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the four source imports by the published module of
`HerbrandH0` and `HerbrandHMinusOne`, keep the source universes, binders,
docstring and body unchanged, and omit the source variable lines (the
definition binds its own `G` and `A` and uses none of them), the open of
`CategoryTheory` and the rest of the source file. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA

/-- The condition that the Herbrand quotient of `A` is defined. -/
def HerbrandQuotientDefined (G : Type uG) (A : Type uA)
    [Group G] [Fintype G] [CommGroup A] [MulDistribMulAction G A]
    (σ : G) : Prop :=
  Finite (HerbrandH0 G A) ∧ Finite (HerbrandHMinusOne G A σ)

end Herbrand
end ProfiniteCohomology

end
end Langlands.NYLL.CyclicCohomology
