/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Core.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandFiniteness.Definitions

/-!
# Targets: finiteness transfer and multiplicativity of Herbrand quotients

Modified by Worker 5264, 15 November 2026: state the source theorems
M119.006 `herbrandQuotientDefined_middle_of_left_right`, M119.010
`herbrandQuotient_multiplicative_of_shortExact` and M119.014
`herbrandQuotient_eq_one_of_finite_module` (in
`CyclicCohomology.ProfiniteCohomology.Herbrand`) of
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandFiniteness.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, replace the source imports by the modules of this port that
define `herbrandQuotient` and `HerbrandQuotientDefined`, keep the source variable
lines, binders and statements unchanged, and omit the proofs, the universe
declaration and the open of `CategoryTheory` (none of these statements uses
them) and the rest of the source file. The unused-variable linter is turned
off for these three declarations only: their propositions do not mention
the hypotheses `hi`, `hj`, `hker`, `hinj`, `hsurj`, `hgen`, `hA` and `hC`.
See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]

set_option linter.unusedVariables false in
/-- Target: Herbrand-quotient multiplicativity, finiteness transfer from the
first and third terms to the middle term. -/
def herbrandQuotientDefined_middle_of_left_rightStatement
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    (hA : HerbrandQuotientDefined G A σ)
    (hC : HerbrandQuotientDefined G C σ) : Prop :=
    HerbrandQuotientDefined G B σ

set_option linter.unusedVariables false in
/-- Target: Herbrand-quotient multiplicativity, Herbrand-quotient
multiplicativity once the three quotients are defined. -/
def herbrandQuotient_multiplicative_of_shortExactStatement
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i)
    (hsurj : ∀ c : C, ∃ b : B, j b = c)
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ)
    [Finite (HerbrandH0 G A)] [Finite (HerbrandHMinusOne G A σ)]
    [Finite (HerbrandH0 G B)] [Finite (HerbrandHMinusOne G B σ)]
    [Finite (HerbrandH0 G C)] [Finite (HerbrandHMinusOne G C σ)] : Prop :=
    herbrandQuotient (G := G) (A := B) σ =
      herbrandQuotient (G := G) (A := A) σ *
        herbrandQuotient (G := G) (A := C) σ

set_option linter.unusedVariables false in
/-- Target: Herbrand-quotient multiplicativity, the finite-module case. -/
def herbrandQuotient_eq_one_of_finite_moduleStatement
    (σ : G) (hgen : ∀ g : G, g ∈ Subgroup.zpowers σ) [Finite A] : Prop :=
    herbrandQuotient (G := G) (A := A) σ = 1

end Herbrand
end ProfiniteCohomology

end
end Langlands.NYLL.CyclicCohomology
