/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.Statements
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.FiniteNormQuotient.U012.Proofs

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.RelativeNorm.U003.Proofs

/-!
# NYLL M039.017: annihilation of the finite norm quotient by the degree

Modified by Worker 520, 16 November 2026: extract M039.017 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/FiniteNormQuotient.lean`
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
`Langlands.NYLL`, import the published statement and M028.003 proof modules,
expand `extensionSubgroup` to its `Subgroup.subgroupOf` body, and state the
theorem through its published target. A leading `show` exposes that target.
Since the earlier M039 proofs are not yet published, their source arguments
are supplied under private implementation names: M039.012 as
`finiteNormClass_eq_zero_iff`, and M039.013/M039.014 combined as
`finiteNormQuotientInductionLocal`. The public proof follows the source
M039.017 steps using those helpers and the published M028.003 theorem.
The induction call supplies its degree-annihilation motive explicitly.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

/-! Integrator, 16 November 2026: reuse the independently accepted public
M039.012 proof and remove the corresponding private copies.
The preceding dated port account describes the original submission. -/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Private source M039.014 induction, with its M039.013 argument inlined. -/
private theorem finiteNormQuotientInductionLocal
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    {motive : FiniteNormQuotient A K L hLK → Prop}
    (q : FiniteNormQuotient A K L hLK)
    (h : ∀ a, motive (finiteNormClass A K L hLK a)) : motive q := by
  change ambientFixedAddSubgroup A K ⧸ finiteNormSubgroup A K L hLK at q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective
    (finiteNormSubgroup A K L hLK) q
  exact h a

/-- Every class in the finite norm quotient is killed by the degree. -/
theorem finiteNormQuotient_degree_nsmul_eq_zero
    (A : Rep ℤ G) (E : DegreeData.FiniteAbstractExtension G)
    (q : FiniteNormQuotient A E.base E.field E.below) :
    finiteNormQuotient_degree_nsmul_eq_zeroStatement A E q := by
  show (E.degree : ℕ) • q = 0
  refine finiteNormQuotientInductionLocal A E.base E.field E.below
    (motive := fun q => (E.degree : ℕ) • q = 0) q ?_
  intro a
  unfold finiteNormClass
  rw [← map_nsmul]
  apply (finiteNormClass_eq_zero_iff A E.base E.field E.below _).2
  refine ⟨fixedFieldInclusion A E.base E.field E.below a, ?_⟩
  exact relativeNorm_fixedFieldInclusion A E a

end
end Langlands.NYLL.ClassFormation
