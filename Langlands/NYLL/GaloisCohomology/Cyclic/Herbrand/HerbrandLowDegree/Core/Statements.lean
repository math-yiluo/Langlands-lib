/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Definitions

/-!
# Targets: the Herbrand quotient as a ratio, its triviality and multiplicativity

Modified by Worker 5264, 15 November 2026: state the source theorems
M118.002 `herbrandQuotient_eq_card_ratio`, M118.003
`herbrandQuotient_eq_one_of_card_eq`, M118.004
`herbrandQuotient_finite_module_eq_one` and M118.005
`herbrandQuotient_exact_multiplicative` (in
`CyclicCohomology.ProfiniteCohomology.Herbrand`) of
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Core.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, replace the source imports by the module of this port that
defines `herbrandQuotient`, keep the source universes, variable lines, binders and
statements unchanged, and omit the proofs and the rest of the source file.
The unused-variable linter is turned off for M118.003, M118.004 and
M118.005 only: their propositions do not mention the hypotheses `hcard`,
`hgen`, `hi`, `hj`, `hker`, `hinj` and `hsurj`. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
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

/-- Target: the Herbrand quotient is definitionally the ratio `#H⁰ / #H^{-1}`. -/
def herbrandQuotient_eq_card_ratioStatement (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)] : Prop :=
    herbrandQuotient (G := G) (A := A) σ =
      (Nat.card (HerbrandH0 G A) : ℚ) /
        (Nat.card (HerbrandHMinusOne G A σ) : ℚ)

set_option linter.unusedVariables false in
/-- Target: if the actual low-degree quotients have the same finite
cardinality, then the Herbrand quotient is `1`. -/
def herbrandQuotient_eq_one_of_card_eqStatement (σ : G)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    (hcard : Nat.card (HerbrandH0 G A) = Nat.card (HerbrandHMinusOne G A σ)) : Prop :=
    herbrandQuotient (G := G) (A := A) σ = 1

set_option linter.unusedVariables false in
/-- Target: Herbrand-quotient theory Herbrand-quotient multiplicativity: the
Herbrand quotient of a finite cyclic module is `1`. -/
def herbrandQuotient_finite_module_eq_oneStatement
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] : Prop :=
    herbrandQuotient (G := G) (A := A) σ = 1

set_option linter.unusedVariables false in
/-- Target: Herbrand-quotient theory Herbrand-quotient multiplicativity:
Herbrand quotient multiplicativity for a short exact sequence of
multiplicative `G`-modules, proved from the standard two-periodic Tate
complex and mathlib's homology long exact sequence. -/
def herbrandQuotient_exact_multiplicativeStatement
    {G A B C : Type}
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c) (σ : G)
    (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] : Prop :=
    herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ

end Herbrand
end ProfiniteCohomology

end
end Langlands.NYLL.CyclicCohomology
