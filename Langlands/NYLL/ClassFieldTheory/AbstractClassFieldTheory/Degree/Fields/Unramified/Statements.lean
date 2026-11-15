/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions

/-!
# Targets: the inertia criterion for unramified abstract, Galois and finite extensions

Modified by Worker 5264, 15 November 2026: state the source theorems
M010.046 `DegreeData.AbstractExtension.isUnramified_iff_inertia_le`, M010.063
`DegreeData.GaloisSubextension.isUnramified_iff_inertia_le` and M010.075
`DegreeData.FiniteAbstractExtension.isUnramified_iff_inertia_le` of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean` at
fbd320cd8b1b06487c58227e92eb135794267709 as Prop-valued Statement
definitions. Prefix the namespace with `Langlands.NYLL`, append `Statement`
to the names, replace the source imports by the published modules of
`GaloisSubextension` and `FiniteAbstractExtension` (which import that of
`AbstractExtension.IsUnramified`), keep the source universe, variables,
binders and statements unchanged, and omit the proofs, the open of
`CyclicCohomology` (none of its names occur in these statements) and the
rest of the source file. See the paired Markdown and `licenses/NYLL/LICENSE`
and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace AbstractExtension

/-- Target: an extension is unramified exactly when the inertia subgroup of
its base is contained in the subgroup representing its field.  The
containment needed to form the extension is carried by `E`. -/
def isUnramified_iff_inertia_leStatement (E : AbstractExtension G) (D : DegreeData G) : Prop :=
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup

end AbstractExtension

namespace GaloisSubextension

variable {K : ClosedSubgroup G}

/-- Target: unramifiedness is the canonical inertia-containment condition. -/
def isUnramified_iff_inertia_leStatement (L : GaloisSubextension K)
    (D : DegreeData G) : Prop :=
    L.IsUnramified D ↔
      K.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ L.field.toSubgroup

end GaloisSubextension

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

/-- Target: finite unramified extensions satisfy the same inertia-containment
characterization as their underlying abstract extensions. -/
def isUnramified_iff_inertia_leStatement (D : DegreeData G) : Prop :=
    E.IsUnramified D ↔
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup

end FiniteAbstractExtension

end DegreeData

end
end Langlands.NYLL.ClassFormation
