/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements

/-!
# NYLL M026.012: the underlying element of the normal-extension action

Modified by Worker 5014, 14 November 2026: extract the theorem
`normalExtensionAction_coe` (M026.012) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 into this focused module, prefix its
namespace with `Langlands.NYLL`, replace the source imports by the published
statement module, state its type through the published
`normalExtensionAction_coeStatement`, and omit the source `@[simp]` attribute
(the type is now the Prop-valued target). The source proof term `rfl` is
retained unchanged. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

open KummerTheory

open CyclicCohomology

-- Mathlib's `Rep ℤ G` currently fixes the acting group to universe zero.
variable {G : IntegralRepGroupType} [Group G] [TopologicalSpace G]

/--
Establishes the identity `((normalExtensionAction A K L hLK hnormal k a : ambientFixedAddSubgroup
A L) : A.V) = A.ρ k.1 a.1`.
-/
theorem normalExtensionAction_coe
    (A : Rep ℤ G) (K L : ClosedSubgroup G)
    (hLK : L.toSubgroup ≤ K.toSubgroup)
    (hnormal : (extensionSubgroup K L hLK).Normal)
    (k : K.toSubgroup) (a : ambientFixedAddSubgroup A L) :
    normalExtensionAction_coeStatement A K L hLK hnormal k a :=
  rfl

end Langlands.NYLL.ClassFormation
