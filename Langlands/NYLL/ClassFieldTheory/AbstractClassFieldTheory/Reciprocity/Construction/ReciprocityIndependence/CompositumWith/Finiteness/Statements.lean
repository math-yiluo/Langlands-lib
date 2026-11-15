/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.ReciprocityIndependence.CompositumWith.Definitions

/-!
# Targets: finiteness and normality of the compositum with a field

Modified by Worker 5264, 15 November 2026: state the source theorems M033.012
`FiniteIntermediateField.compositumWith_finite`, M033.013
`FiniteIntermediateField.compositumWith_normal` and M033.014
`FiniteIntermediateField.compositumWith_finite_over_base` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/ReciprocityIndependence.lean`
at fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to each name, replace the source imports by the focused published import,
and omit the proofs and the rest of the source file. The proof term
`M.compositumWith_le_right S` (the unpublished proof of M033.010) is
replaced by its source proof `inf_le_right` written inline; by proof
irrelevance the propositions are the same. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

universe u

namespace Langlands.NYLL.ClassFormation

open CyclicCohomology

noncomputable section

section groupTheoreticRefinements

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteIntermediateField

set_option linter.unusedVariables false in
/-- Target: the compositum of the two finite refinements has finite relative
quotient. -/
def compositumWith_finiteStatement
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup) : Prop :=
  Finite (S.toSubgroup ⧸
      extensionSubgroup S (M.compositumWith S)
        (show (M.compositumWith S).toSubgroup ≤ S.toSubgroup from inf_le_right))

set_option linter.unusedVariables false in
/-- Target: the compositum of normal refinements is again normal. -/
def compositumWith_normalStatement
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup)
    [hMnormal : (extensionSubgroup K M.field M.below).Normal] : Prop :=
  (extensionSubgroup S (M.compositumWith S)
      (show (M.compositumWith S).toSubgroup ≤ S.toSubgroup from
        inf_le_right)).Normal

set_option linter.unusedVariables false in
/-- Target: the compositum of two finite extensions of `K` is finite over
`K`. Contravariantly this is the finite-index theorem for an intersection. -/
def compositumWith_finite_over_baseStatement
    {E K : ClosedSubgroup G} (M : FiniteIntermediateField E K)
    (S : ClosedSubgroup G) (hSK : S.toSubgroup ≤ K.toSubgroup)
    [hSfinite : Finite (K.toSubgroup ⧸ extensionSubgroup K S hSK)] : Prop :=
  Finite (K.toSubgroup ⧸ extensionSubgroup K (M.compositumWith S)
      ((show (M.compositumWith S).toSubgroup ≤ S.toSubgroup from
        inf_le_right).trans hSK))

end FiniteIntermediateField

end groupTheoreticRefinements

end

end Langlands.NYLL.ClassFormation
