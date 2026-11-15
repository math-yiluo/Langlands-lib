/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions

/-!
# The Herbrand quotient

Modified by Worker 5264, 15 November 2026: port the source definition
M118.001 `CyclicCohomology.ProfiniteCohomology.Herbrand.herbrandQuotient` of
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, replace the two source imports by the published module of
`HerbrandH0` and `HerbrandHMinusOne`, keep the source universes, variable
lines, binders, docstring and body unchanged, and omit the rest of the
source file. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

open scoped BigOperators

namespace ProfiniteCohomology
namespace Herbrand

universe uG uA uB uC

variable {G : Type uG} {A : Type uA} {B : Type uB} {C : Type uC}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

/-- Herbrand-quotient theory the Herbrand-quotient definition: the Herbrand quotient of the actual
low-degree multiplicative Tate quotients.  The finiteness assumptions prevent
`Nat.card` from silently taking the value `0` on infinite quotients. -/
noncomputable def herbrandQuotient (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)] : ℚ :=
  (Nat.card (HerbrandH0 G A) : ℚ) / (Nat.card (HerbrandHMinusOne G A σ) : ℚ)

end Herbrand
end ProfiniteCohomology

end
end Langlands.NYLL.CyclicCohomology
