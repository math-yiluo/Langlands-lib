/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Adapted by Worker 85, 14 November 2026: extracted, without its proof, the
type of the source theorem
LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eq (inventory
M166.001) as the Prop-valued definition
Langlands.NYLL.LocalClassFieldTheory.relativeNorm_coe_eq_of_closedSubgroup_eqStatement.
The theorem's binders become the binders of the definition, unchanged and in
the source order; the proposition is unchanged. The file's section variables
K and Ω do not occur in the theorem and are not binders. The added
set_option linter.unusedVariables false only silences the linter for the
hypotheses hB, hC and hx, which the proposition does not mention. The namespace is
prefixed with Langlands.NYLL; the NYLL imports are replaced by the published
modules defining the names used. All other source declarations are omitted.
The retained license and notice are licenses/NYLL/LICENSE and
licenses/NYLL/NOTICE.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Relative norms along equal closed subgroups: congruence target

Source: Naganori Yamaguchi, ClassFieldTheory, commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/AbstractFixedFieldNorm.lean`,
lines 21–28 (namespace and opens) and 34–54 (docstring and theorem
type of inventory M166.001).
-/

namespace Langlands.NYLL.LocalClassFieldTheory
open CyclicCohomology KummerTheory ClassFormation

set_option linter.unusedVariables false in
/-- Target of the source theorem `relativeNorm_coe_eq_of_closedSubgroup_eq`
(M166.001): the underlying value of a relative norm is unchanged when its two
closed-subgroup indices and its fixed coefficient are transported along
equalities. -/
def relativeNorm_coe_eq_of_closedSubgroup_eqStatement
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
    (hx : x.1 = x'.1) : Prop :=
  ((relativeNorm A B C hCB x : ambientFixedAddSubgroup A B) : A.V) =
    ((relativeNorm A B' C' hC'B' x' :
      ambientFixedAddSubgroup A B') : A.V)

end Langlands.NYLL.LocalClassFieldTheory
