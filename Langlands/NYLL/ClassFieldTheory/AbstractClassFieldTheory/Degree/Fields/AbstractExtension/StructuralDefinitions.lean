/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.AbstractExtension.Definitions

/-!
# NYLL M010: abstract towers and ramification predicates

Modified by Worker 198: extract the source units listed in the paired Markdown,
prefix their namespace with Langlands.NYLL, and use focused published imports.
The Markdown records all statement conversions and construction substitutions.
See licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace AbstractExtension

/-- A composable tower of abstract extensions, represented by three closed
subgroups and the two adjacent containments. -/
structure Tower (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup representing the top field. -/
  top : ClosedSubgroup G
  /-- The closed subgroup representing the middle field. -/
  middle : ClosedSubgroup G
  /-- The closed subgroup representing the base field. -/
  base : ClosedSubgroup G
  /-- Contravariant containment for the top-to-middle extension. -/
  top_le_middle : top.toSubgroup ≤ middle.toSubgroup
  /-- Contravariant containment for the middle-to-base extension. -/
  middle_le_base : middle.toSubgroup ≤ base.toSubgroup

namespace Tower

variable (T : Tower G)

/-- The upper extension in a tower. -/
def topExtension : AbstractExtension G where
  field := T.top
  base := T.middle
  below := T.top_le_middle

/-- The lower extension in a tower. -/
def baseExtension : AbstractExtension G where
  field := T.middle
  base := T.base
  below := T.middle_le_base

/-- The composite extension in a tower. -/
def totalExtension : AbstractExtension G where
  field := T.top
  base := T.base
  below := T.top_le_middle.trans T.middle_le_base

end Tower

/-- An abstract extension is unramified when the inertia subgroup of its base
is already contained in the subgroup representing its field.  This
containment is the definition; it does not pass through a natural-valued index
that would encode an infinite index as zero. -/
def IsUnramified (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤ E.field.toSubgroup

/-- An abstract extension is totally ramified when the degree image of its
base is contained in the degree image of its field. -/
def IsTotallyRamified (E : AbstractExtension G) (D : DegreeData G) : Prop :=
  E.base.toSubgroup.map D.degree.toMonoidHom ≤
    E.field.toSubgroup.map D.degree.toMonoidHom

end AbstractExtension
end DegreeData

end
end Langlands.NYLL.ClassFormation
