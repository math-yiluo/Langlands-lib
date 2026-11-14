/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M022.002
(extensionFixedRepresentation_quotient_mk_apply_val) from
Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published KummerAbelianAssembly U002
Statements module. Keep `open CyclicCohomology`, the noncomputable section,
the section variable line, the docstring and the `@[simp]` attribute. Write
the normality instance binder with the Mathlib body
`M.toSubgroup.subgroupOf K.toSubgroup` of the source abbreviation
`extensionSubgroup K M hMK`, as the published statement does, and state the
theorem as the published Statement applied to the source parameters. The
proof `rfl` is unchanged. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U002.Statements

/-!
# The quotient action on an invariant subtype at a representative

The proof that the quotient action on `A_M` by `G_K / G_M`, evaluated at the
class of `k : G_K`, is the ambient action of `k`.
-/

namespace Langlands.NYLL.KummerTheory

open CyclicCohomology

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- The quotient action on an invariant subtype is the original ambient
action after choosing a representative in `G_K`. -/
@[simp]
theorem extensionFixedRepresentation_quotient_mk_apply_val
    (A : Rep ℤ G) (K M : ClosedSubgroup G)
    (hMK : M.toSubgroup ≤ K.toSubgroup)
    [hnormal : (M.toSubgroup.subgroupOf K.toSubgroup).Normal]
    (a : (extensionFixedRepresentation A K M hMK hnormal).V)
    (k : K.toSubgroup) :
    extensionFixedRepresentation_quotient_mk_apply_valStatement A K M hMK a k := rfl

end

end Langlands.NYLL.KummerTheory
