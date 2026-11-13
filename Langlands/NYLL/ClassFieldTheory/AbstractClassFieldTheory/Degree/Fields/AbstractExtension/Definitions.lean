/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# The NYLL abstract-extension data

Modified by Worker 120: extract M010.028–031 and .033–034 from the pinned
Fields.lean; prefix the namespace and use focused published initial data.
Replace the source extensionSubgroup abbreviation by its exact Mathlib
Subgroup.subgroupOf body. Preserve the full source extension object,
coset and cardinal constructions, parameters and universes.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- An abstract field extension, including the containment which makes the
notation `L / K` meaningful in the closed-subgroup model.  Keeping this proof
in the object prevents predicates for extensions from being formed for
unrelated closed subgroups. -/
structure AbstractExtension (G : Type*) [Group G] [TopologicalSpace G] where
  /-- The closed subgroup contravariantly representing the extension field. -/
  field : ClosedSubgroup G
  /-- The closed subgroup contravariantly representing the base field. -/
  base : ClosedSubgroup G
  /-- Contravariance turns the field inclusion into this subgroup inclusion. -/
  below : field.toSubgroup ≤ base.toSubgroup

namespace AbstractExtension

/-- The subgroup of the base group represented by the extension field.  This
projection packages the proof-dependent `subgroupOf` construction behind the
extension object. -/
def subgroup (E : AbstractExtension G) : Subgroup E.base.toSubgroup :=
  E.field.toSubgroup.subgroupOf E.base.toSubgroup

/-- The actual relative coset space of an abstract extension. -/
def quotient (E : AbstractExtension G) : Type u :=
  E.base.toSubgroup ⧸ E.subgroup

/-- The honest cardinal degree of an arbitrary abstract extension.  Unlike
the raw natural-valued subgroup index, this does not encode infinity as zero. -/
noncomputable def degreeCardinal (E : AbstractExtension G) : Cardinal :=
  relativeIndexCardinal E.below


/-- The relative residue degree of an arbitrary abstract extension, as the
cardinality of the actual coset type of degree images.  This is the canonical
general API: an infinite residue degree remains an infinite cardinal. -/
noncomputable def relativeResidueDegreeCardinal
    (E : AbstractExtension G) (D : DegreeData G) : Cardinal :=
  relativeIndexCardinal (Subgroup.map_mono (f := D.degree.toMonoidHom) E.below)

/-- The relative ramification index of an arbitrary abstract extension, as
the cardinality of the actual coset type inside the degree kernel.  In
particular, infinity is not encoded as zero. -/
noncomputable def relativeRamificationIndexCardinal
    (E : AbstractExtension G) (D : DegreeData G) : Cardinal :=
  relativeIndexCardinal
    (show E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker ≤
      E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker from
        inf_le_inf E.below le_rfl)

end AbstractExtension
end DegreeData

end
end Langlands.NYLL.ClassFormation
