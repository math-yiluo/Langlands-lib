/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.Statements

/-!
# NYLL M026.006: membership in the absolute extension subgroup

Modified by Worker 5014, 14 November 2026: extract the private source theorem
`ClassFormation.mem_absoluteExtension` (M026.006) from
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/NormLaws.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 into this focused module, make it
public under the port-internal name `Langlands.NYLL.PortInternal.M026.d006`,
replace the source imports by the published statement module, and state its
type through the published `Langlands.NYLL.PortInternal.M026.d006Statement`.
The source proof term `Iff.rfl` is retained unchanged. See the paired Markdown
and `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

/-- The private source theorem `ClassFormation.mem_absoluteExtension`: an
element of the absolute subgroup lies in the relative subgroup of `K` over the
base field exactly when its underlying element lies in `K`. -/
theorem _root_.Langlands.NYLL.PortInternal.M026.d006 {G : Type*} [Group G]
    [TopologicalSpace G]
    (K : ClosedSubgroup G)
    (x : (baseField G).toSubgroup) :
    Langlands.NYLL.PortInternal.M026.d006Statement K x :=
  Iff.rfl

end Langlands.NYLL.ClassFormation
