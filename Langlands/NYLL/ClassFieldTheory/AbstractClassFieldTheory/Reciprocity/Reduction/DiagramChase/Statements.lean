/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.Algebra.Exact.Basic
import Mathlib.GroupTheory.Commutator.Basic

/-!
# NYLL abstract reciprocity: diagram-chase targets of the reductions

Modified by Worker 68, 13 November 2026: extract the asserted types of M077.032, lines
670–683; M077.033, lines 707–722; and M077.034, lines 751–755 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Reduction.lean` at
`fbd320cd8b1b06487c58227e92eb135794267709` as Prop-valued definitions without their proofs.
Prefix the namespace with `Langlands.NYLL`, append `Statement` to each theorem name and use
focused Mathlib imports. See the paired Markdown for all changes and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE` for retained attribution.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

-- Preserve the source hypothesis names even when the conclusions do not mention them.
set_option linter.unusedVariables false in
/-- Target of `abstractReciprocity_surjective_of_exact_diagram`: the middle vertical arrow is
surjective when the two outside vertical arrows are surjective, the top-right arrow is
surjective, and the bottom row is exact. -/
def abstractReciprocity_surjective_of_exact_diagramStatement
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexact : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Surjective r₀)
    (hr₁ : Function.Surjective r₁) : Prop :=
    Function.Surjective r

set_option linter.unusedVariables false in
/-- Target of `abstractReciprocity_bijective_of_exact_diagram`: if both outside reciprocity
arrows are bijective and the first lower arrow is injective, then the middle reciprocity arrow
is bijective. -/
def abstractReciprocity_bijective_of_exact_diagramStatement
    {Q₀ Q Q₁ B₀ B B₁ : Type*}
    [AddGroup Q₀] [AddGroup Q] [AddGroup Q₁]
    [AddGroup B₀] [AddGroup B] [AddGroup B₁]
    (iQ : Q₀ →+ Q) (pQ : Q →+ Q₁)
    (iB : B₀ →+ B) (pB : B →+ B₁)
    (r₀ : Q₀ →+ B₀) (r : Q →+ B) (r₁ : Q₁ →+ B₁)
    (hexactQ : Function.Exact iQ pQ)
    (hexactB : Function.Exact iB pB)
    (hpQ : Function.Surjective pQ)
    (hiB : Function.Injective iB)
    (hleft : ∀ q, r (iQ q) = iB (r₀ q))
    (hright : ∀ q, pB (r q) = r₁ (pQ q))
    (hr₀ : Function.Bijective r₀)
    (hr₁ : Function.Bijective r₁) : Prop :=
    Function.Bijective r

set_option linter.unusedVariables false in
/-- Target of `abstractReciprocity_commutator_mem_kernel`: every additive homomorphism from a
group into an abelian group kills the commutator subgroup. -/
def abstractReciprocity_commutator_mem_kernelStatement
    {Q : Type*} {B : Type*} [Group Q] [AddCommGroup B]
    (r : Additive Q →+ B) (q : Q)
    (hq : q ∈ commutator Q) : Prop :=
    r (Additive.ofMul q) = 0

end
end Langlands.NYLL.ClassFormation
