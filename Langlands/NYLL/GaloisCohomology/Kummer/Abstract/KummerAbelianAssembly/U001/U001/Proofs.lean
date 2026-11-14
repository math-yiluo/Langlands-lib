/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M022.001 (mem_extensionSubgroup_iff) from
Nyll/GaloisCohomology/Kummer/Abstract/KummerAbelianAssembly.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published KummerAbelianAssembly U001
Statements module. Omit the unused `open CyclicCohomology` and the section
variable line, which this theorem shadows by its own `{G : Type*}` binder;
keep the noncomputable section, the docstring and the `@[simp]` attribute,
and state the theorem as the published Statement applied to the source
parameters. The proof `Iff.rfl` is unchanged. The original LICENSE and NOTICE
are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerAbelianAssembly.U001.Statements

/-!
# Membership in the extension subgroup

The proof that membership in `G_L`, regarded as a subgroup of `G_K`, is
ambient membership in `G_L`.
-/

namespace Langlands.NYLL.KummerTheory

noncomputable section

/-- Membership in `G_L`, regarded as a subgroup of `G_K`, is the same as
ambient membership in the closed subgroup `G_L`. -/
@[simp]
theorem mem_extensionSubgroup_iff
    {G : Type*} [Group G] [TopologicalSpace G]
    (K L : ClosedSubgroup G) (hLK : L.toSubgroup ≤ K.toSubgroup)
    (k : K.toSubgroup) :
    mem_extensionSubgroup_iffStatement K L hLK k :=
  Iff.rfl

end

end Langlands.NYLL.KummerTheory
