/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Statements

/-!
# NYLL M039.016: evaluation of the quotient lift on a finite norm class

Modified by Worker 520, 16 November 2026: extract M039.016 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, import the published statement module, expand
`extensionSubgroup` to its `Subgroup.subgroupOf` body, and state the theorem
through the published `finiteNormQuotientLift_finiteNormClassStatement`.
The proof and the `simp` attribute are unchanged.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The quotient lift evaluates on a class by its representative. -/
@[simp]
theorem finiteNormQuotientLift_finiteNormClass
    {B : Type*} [AddCommGroup B]
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (f : ambientFixedAddSubgroup A K →+ B)
    (hf : finiteNormSubgroup A K L hLK ≤ f.ker)
    (a : ambientFixedAddSubgroup A K) :
    finiteNormQuotientLift_finiteNormClassStatement A K L hLK f hf a := by
  rfl

end
end Langlands.NYLL.ClassFormation
