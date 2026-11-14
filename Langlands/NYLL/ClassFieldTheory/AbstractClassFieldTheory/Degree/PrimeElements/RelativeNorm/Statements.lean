/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions

/-!
# Relative norms of included and trivial-extension elements: statement targets

Modified by Worker 96, 14 November 2026: extract the statements of M028.003
and M028.004 from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean`
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
`Langlands.NYLL`, import the published relative norm, fixed-field inclusion
and finite abstract extension modules, replace `extensionSubgroup K K le_rfl`
by its exact `Subgroup.subgroupOf` body, and publish Prop-valued definitions
with the `Statement` suffix. The source proofs, the simp attribute and the
unused section variables `D` and `A` are omitted.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target: the norm of an element already fixed over `K` is its `[L:K]`-fold
sum. -/
def relativeNorm_fixedFieldInclusionStatement
    (A : Rep ℤ G) (E : DegreeData.FiniteAbstractExtension G)
    (a : ambientFixedAddSubgroup A E.base) : Prop :=
    relativeNorm A E.base E.field E.below
        (fixedFieldInclusion A E.base E.field E.below a) =
      (E.degree : ℕ) • a

/-- Target: the norm of the trivial extension is the identity. -/
def relativeNorm_selfStatement
    (A : Rep ℤ G) (K : ClosedSubgroup G)
    [Finite (K.toSubgroup ⧸ (K.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A K) : Prop :=
    relativeNorm A K K le_rfl a = a

end
end Langlands.NYLL.ClassFormation
