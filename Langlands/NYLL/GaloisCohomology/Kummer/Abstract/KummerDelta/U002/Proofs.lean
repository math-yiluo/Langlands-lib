/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M023.002 (mem_ambientFixedAddSubgroup_iff) from
Nyll/GaloisCohomology/Kummer/Abstract/KummerDelta.lean (lines 46–53)
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published KummerDelta U002 Statements
module. Keep the section variable line, the noncomputable section, the
docstring, the theorem name and binders, and state the theorem as the
published Statement applied to the source parameters. Omit the `simp`
attribute, because the stated type is the unexpanded proposition constant
rather than an equivalence, the unused `open CyclicCohomology` and all other
source declarations. The proof `Iff.rfl` is unchanged. The original LICENSE
and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Kummer.Abstract.KummerDelta.U002.Statements

/-!
# Membership in the ambient fixed additive subgroup

The proof that an ambient coefficient element lies in the subgroup fixed by a
closed subgroup `H` exactly when every element of `H` fixes it.
-/

namespace Langlands.NYLL.KummerTheory

noncomputable section

variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/-- Membership in the ambient fixed subgroup is equivalent to invariance under every
subgroup element. -/
theorem mem_ambientFixedAddSubgroup_iff
    (A : Rep ℤ G) (H : ClosedSubgroup G) (a : A.V) :
    mem_ambientFixedAddSubgroup_iffStatement A H a :=
  Iff.rfl

end

end Langlands.NYLL.KummerTheory
