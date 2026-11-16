/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Statements

/-!
# NYLL M118.003: equal cardinalities give Herbrand quotient one

Modified by Worker 5264, 15 November 2026: prove the published target
`herbrandQuotient_eq_one_of_card_eqStatement` (M118.003) by the source proof
of `herbrandQuotient_eq_one_of_card_eq` in
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean` at
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, give the theorem the published proposition as its type,
begin the proof with `show` stating it unfolded, replace the source imports
by the published statement module and omit the rest of the source file.
See the paired Markdown and `licenses/NYLL/LICENSE` and
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

/-- If the actual low-degree quotients have the same finite cardinality, then
the Herbrand quotient is `1`. -/
theorem herbrandQuotient_eq_one_of_card_eq (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    (hcard : Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ)) :
    herbrandQuotient_eq_one_of_card_eqStatement (G := G) (A := A) σ hcard := by
  show herbrandQuotient (G := G) (A := A) σ = 1
  have hden : ((Nat.card (HerbrandHMinusOne G A σ) : ℚ) ≠ 0) :=
    Nat.cast_ne_zero.mpr (Finite.card_pos (α := HerbrandHMinusOne G A σ)).ne'
  unfold herbrandQuotient
  rw [hcard]
  exact div_self hden

end Herbrand
end ProfiniteCohomology

end

end Langlands.NYLL.CyclicCohomology
