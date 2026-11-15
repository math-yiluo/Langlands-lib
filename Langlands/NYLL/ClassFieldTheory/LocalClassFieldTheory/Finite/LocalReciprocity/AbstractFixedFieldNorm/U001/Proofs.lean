/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 368, 15 November 2026: adapt the source theorem
LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eq (inventory
M166.001, lines 34–63 of
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709) to prove the
published target
Langlands.NYLL.LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eqStatement;
prefix the namespace with Langlands.NYLL; replace the source imports by the
published target; add `unfold` of the target before the source tactic
proof, which is otherwise unchanged. The retained license and notice are
licenses/NYLL/LICENSE and licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.AbstractFixedFieldNorm.U001.Statements

/-!
# Relative norms along equal closed subgroups: congruence

The proof of the NYLL M166.001 theorem for the exact published target.
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open CyclicCohomology KummerTheory ClassFormation

/-- The underlying value of a relative norm is unchanged when its two
closed-subgroup indices and its fixed coefficient are transported along
equalities.  Keeping this congruence explicit avoids dependent rewriting
through the inclusion proof carried by `relativeNorm`. -/
theorem relativeNorm_coe_eq_of_closedSubgroup_eq
    {G : Type} [Group G] [TopologicalSpace G]
    (A : Rep ℤ G)
    (B B' C C' : ClosedSubgroup G)
    (hCB : C.toSubgroup ≤ B.toSubgroup)
    (hC'B' : C'.toSubgroup ≤ B'.toSubgroup)
    [hfinite : Finite
      (B.toSubgroup ⧸ extensionSubgroup B C hCB)]
    [hfinite' : Finite
      (B'.toSubgroup ⧸ extensionSubgroup B' C' hC'B')]
    (hB : B = B') (hC : C = C')
    (x : ambientFixedAddSubgroup A C)
    (x' : ambientFixedAddSubgroup A C')
    (hx : x.1 = x'.1) :
    relativeNorm_coe_eq_of_closedSubgroup_eqStatement A B B' C C' hCB hC'B'
      hB hC x x' hx := by
  unfold relativeNorm_coe_eq_of_closedSubgroup_eqStatement
  subst B'
  subst C'
  have hle : hCB = hC'B' := Subsingleton.elim _ _
  subst hC'B'
  have hfin : hfinite = hfinite' := Subsingleton.elim _ _
  subst hfinite'
  have hxx' : x = x' := Subtype.ext hx
  subst x'
  rfl

end Langlands.NYLL.LocalClassFieldTheory
