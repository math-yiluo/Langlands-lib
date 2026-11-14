/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ClassFieldAxiom.Definitions

/-!
# Abstract reciprocity: the three halves of the class field axiom

Adapted by Worker 90 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/ClassFieldAxiom.lean`,
lines 64–98 (M072.003–M072.005).

Modifications by Worker 90: the three source theorems become Prop-valued
`Statement` definitions whose bodies are the source conclusions, with the
source section variables `{G : IntegralRepGroupType} [Group G]
[TopologicalSpace G]` and `{A : Rep ℤ G}` and the explicit binders
`hcf`, `K`, `E` in the source order; prefix the namespace with
`Langlands.NYLL`; import the sibling definitions module; omit the proofs;
silence the unused-variable linter for `hcf`, which the conclusions do not
mention. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

open CategoryTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

namespace SatisfiesClassFieldAxiom

variable {A : Rep ℤ G}

set_option linter.unusedVariables false in
/-- Target for M072.003: the degree-zero half of the class-field axiom for a
bundled cyclic extension. -/
def tateHZero_cardStatement
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) : Prop :=
  Nat.card (tateCohomology (E.fixedRepresentation A) 0) =
    (E.toFiniteAbstractExtension.degree : ℕ)

set_option linter.unusedVariables false in
/-- Target for M072.004: the degree-minus-one half of the class-field axiom
for a bundled cyclic extension. -/
def tateHMinusOne_cardStatement
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) : Prop :=
  Nat.card (tateCohomology (E.fixedRepresentation A) (-1)) = 1

set_option linter.unusedVariables false in
/-- Target for M072.005: the order-one assertion in the class-field axiom
gives actual vanishing of `H⁻¹(G(L/K), A_L)`. -/
def tateHMinusOne_isZeroStatement
    (hcf : SatisfiesClassFieldAxiom A)
    (K : FiniteAbstractField G) (E : FiniteCyclicSubextension K) : Prop :=
  Limits.IsZero (tateCohomology (E.fixedRepresentation A) (-1))

end SatisfiesClassFieldAxiom

end Langlands.NYLL.ClassFormation
