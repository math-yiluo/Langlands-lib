/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 395, 14 November 2026 UTC:
Extract only the proof of M028.002 (fixedFieldInclusion_coe) from
Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/PrimeElements.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published PrimeElements Statements
module. Omit the unused `open CyclicCohomology` and the unused second section
variable line, keep `open KummerTheory`, the noncomputable section, the first
section variable line, the docstring and the `@[simp]` attribute, and state
the theorem as the published Statement applied to the source parameters. The
proof `rfl` is unchanged. The original LICENSE and NOTICE are retained in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.PrimeElements.Statements

/-!
# Coercion of the fixed-field inclusion

The proof that the inclusion `A_K → A_L` of ambient fixed additive subgroups
does not change the underlying element.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

noncomputable section

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/--
Establishes the identity `((fixedFieldInclusion A K L hLK a : ambientFixedAddSubgroup A L) : A.V)
= a.1`.
-/
@[simp]
theorem fixedFieldInclusion_coe (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (a : ambientFixedAddSubgroup A K) :
    fixedFieldInclusion_coeStatement A K L hLK a :=
  rfl

end

end Langlands.NYLL.ClassFormation
