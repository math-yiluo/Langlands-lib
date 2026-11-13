/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Definitions

/-!
# NYLL M010: extensionality target for finite abstract fields

Modified by Worker 171: extract the source theorem M010.122 from the pinned NYLL
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`, prefix the
namespace with `Langlands.NYLL`, and convert it to the Prop-valued target
`eq_of_field_eqStatement` with the same binders and conclusion; the source
proof is omitted. See the paired Markdown and `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace FiniteAbstractField

/-- Target: a finite abstract field is determined by its underlying closed
subgroup; the finiteness component is proof-irrelevant. -/
def eq_of_field_eqStatement (K L : FiniteAbstractField G)
    (h : K.field = L.field) : Prop :=
  K = L

end FiniteAbstractField

end
end Langlands.NYLL.ClassFormation
