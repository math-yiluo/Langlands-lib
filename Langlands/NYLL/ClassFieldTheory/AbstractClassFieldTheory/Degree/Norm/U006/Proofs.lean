/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 165, 13 November 2026 UTC:
Extract only the proof of M024.006 from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean at
fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published Norm Statements module.
State the theorem as the published Statement applied to the source
parameters and unfold that Statement first. Write the relative coset
subgroup as its published Subgroup.subgroupOf body in place of the
source extensionSubgroup. Replace the original
simp only [relativeCosetAction_mk] step by an explicit definitional
change, so the proof does not depend on the unpublished M024.002 proof;
the original quotient induction and map_add step are retained.
Omit the source noncomputable section, open CyclicCohomology and all
other source declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.Statements

/-!
# Additivity of the relative coset action

The exact proof that the relative coset action at a fixed coset is additive
in the represented fixed coefficient.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The relative coset action is additive in the represented fixed element. -/
theorem relativeCosetAction_add
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a b : ambientFixedAddSubgroup A L)
    (q : K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup)) :
    relativeCosetAction_addStatement A K L hLK a b q := by
  unfold relativeCosetAction_addStatement
  refine Quotient.inductionOn' q ?_
  intro k
  change A.ρ k.1 (a + b).1 = A.ρ k.1 a.1 + A.ρ k.1 b.1
  exact map_add (A.ρ k.1) a.1 b.1

end Langlands.NYLL.ClassFormation
