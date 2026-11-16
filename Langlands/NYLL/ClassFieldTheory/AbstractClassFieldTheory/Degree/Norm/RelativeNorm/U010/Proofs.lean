/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Norm.RelativeNorm.Statements

/-!
# NYLL M024.010: coercing a relative norm gives the coset-sum norm value

Modified by Worker 744, 16 November 2026 UTC: extract only the proof of
M024.010 from `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Norm.lean`
(lines 163–172) at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the
namespace with `Langlands.NYLL`, import only the published RelativeNorm
Statements module, and give the theorem the published Statement applied to
the source parameters as its type. Write `extensionSubgroup K L hLK` as its
exact `Subgroup.subgroupOf` body. The source proof term `rfl` is retained.
The `@[simp]` attribute, the source `noncomputable section`,
`open CyclicCohomology`, `open scoped BigOperators` and all other source
declarations are omitted; `open KummerTheory` is kept.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

-- Mathlib's `Rep ℤ G` currently fixes `G` to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Coercing a relative norm gives the explicit sum over quotient representatives. -/
theorem relativeNorm_apply_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    [Finite (K.toSubgroup ⧸ (L.toSubgroup.subgroupOf K.toSubgroup))]
    (a : ambientFixedAddSubgroup A L) :
    relativeNorm_apply_coeStatement A K L hLK a :=
  rfl

end Langlands.NYLL.ClassFormation
