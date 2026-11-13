/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.IntegralRepUniverse
import Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.Extension.Definitions

/-!
# Quotient-action evaluation target

Modified by Worker 291, 13 November 2026: extract the statement of M022.002
from NYLL's `KummerAbelianAssembly.lean` at
fbd320cd8b1b06487c58227e92eb135794267709, prefix its namespace with
`Langlands.NYLL`, and replace the theorem by a Prop-valued definition with
the `Statement` suffix. Reuse the published extension fixed representation
and expand `CyclicCohomology.extensionSubgroup` to its Mathlib
`Subgroup.subgroupOf` body as directed by Task 5831. The source's complete
telescope and actual quotient action are retained.
See the paired Markdown and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.KummerTheory

open CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Target for the quotient action on an invariant subtype evaluated at a representative. -/
def extensionFixedRepresentation_quotient_mk_apply_valStatement
    (A : Rep ℤ G) (K M : ClosedSubgroup G)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (a : (extensionFixedRepresentation A K M hMK hnormal).V)
    (k : K.toSubgroup) : Prop :=
  ((extensionFixedRepresentation A K M hMK hnormal).ρ
    ((QuotientGroup.mk' (M.toSubgroup.subgroupOf K.toSubgroup)) k) a).1 =
    A.ρ k.1 a.1

end

end Langlands.NYLL.KummerTheory
