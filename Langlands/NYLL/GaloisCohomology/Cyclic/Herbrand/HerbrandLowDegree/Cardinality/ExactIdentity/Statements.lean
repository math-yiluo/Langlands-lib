/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.Basic.HerbrandQuotients.Definitions

/-!
# Target: the cardinality identity of the Herbrand exact hexagon

Modified by Worker 5264, 15 November 2026: state the source theorem M117.021
`CyclicCohomology.ProfiniteCohomology.Herbrand.herbrand_exact_cardinality_identity`
of `Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/Cardinality.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as a Prop-valued Statement
definition. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the name, replace the source imports by the published module of
`HerbrandH0` and `HerbrandHMinusOne`, keep the source variable line
`variable {G A B C : Type}`, binders and statement unchanged, and omit the
proof, the open of `CategoryTheory` (none of its names occurs in this
statement) and the rest of the source file. The unused-variable linter is
turned off for this declaration only: the proposition does not mention the
hypotheses `hi`, `hj`, `hker`, `hinj`, `hsurj` and `hgen`. See the paired
Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

namespace ProfiniteCohomology
namespace Herbrand

variable {G A B C : Type}

set_option linter.unusedVariables false in
/-- Target: the finite-cardinality identity supplied directly by mathlib's
standard two-periodic Tate exact sequence for a finite cyclic group. -/
def herbrand_exact_cardinality_identityStatement
    [Group G] [Fintype G]
    [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
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
    Nat.card (HerbrandH0 G B) *
        Nat.card (HerbrandHMinusOne G A σ) *
        Nat.card (HerbrandHMinusOne G C σ) =
      Nat.card (HerbrandH0 G A) *
        Nat.card (HerbrandH0 G C) *
        Nat.card (HerbrandHMinusOne G B σ)

end Herbrand
end ProfiniteCohomology

end
end Langlands.NYLL.CyclicCohomology
