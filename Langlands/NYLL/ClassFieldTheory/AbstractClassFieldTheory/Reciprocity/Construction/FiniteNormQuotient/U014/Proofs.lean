/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Statements

/-!
# NYLL M039.014: induction on a finite norm class

Modified by Worker 520, 16 November 2026: extract M039.014 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, import the published statement module, expand
`extensionSubgroup` to its `Subgroup.subgroupOf` body, and state the theorem
through its published `induction_onStatement`. Add a leading `show` to expose
that target. Since M039.013 is not yet published, use its unchanged source
proof privately as `finiteNormClassSurjectiveLocal`. The final two proof
steps are the source's. Omit `elab_as_elim`: Lean rejects that attribute
on the named proposition used as the required theorem type.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Private source M039.013 proof, used before its public proof is published. -/
private theorem finiteNormClassSurjectiveLocal
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))] :
    Function.Surjective (finiteNormClass A K L hLK) := by
  intro q
  change ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK at q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (finiteNormSubgroup A K L hLK) q
  exact ⟨a, rfl⟩

/-- Eliminate a finite norm-quotient class through an ambient representative. -/
theorem FiniteNormQuotient.induction_on
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    {motive : FiniteNormQuotient A K L hLK → Prop}
    (q : FiniteNormQuotient A K L hLK)
    (h : ∀ a, motive (finiteNormClass A K L hLK a)) :
    FiniteNormQuotient.induction_onStatement A K L hLK q h := by
  show motive q
  obtain ⟨a, rfl⟩ := finiteNormClassSurjectiveLocal A K L hLK q
  exact h a

end
end Langlands.NYLL.ClassFormation
