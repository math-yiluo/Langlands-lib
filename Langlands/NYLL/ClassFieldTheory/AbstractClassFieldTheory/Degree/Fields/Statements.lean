/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# Targets for the initial NYLL degree and field data

Modified by Worker 120: extract M010.004–005, .007, .009, .011, .013, .016
and .019–020 as Prop-valued Statement definitions. Preserve the source
universes, parameter order and hypotheses. Reuse the actual degree, field,
inertia and residue objects; omit source theorem bodies and simp attributes.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Target for the underlying subgroup of the distinguished base field. -/
def baseField_toSubgroupStatement (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  (baseField G).toSubgroup = ⊤

/-- Target for every abstract field lying over the distinguished base field. -/
def le_baseFieldStatement (K : ClosedSubgroup G) : Prop :=
  K.toSubgroup ≤ (baseField G).toSubgroup

namespace DegreeData

/-- Target for the membership criterion in ambient inertia. -/
def mem_inertia_iffStatement (D : DegreeData G) (g : G) : Prop :=
  g ∈ D.inertia ↔ D.degree g = 1

/-- Target for evaluation of the restricted degree. -/
def restrictedDegree_applyStatement (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) : Prop :=
  D.restrictedDegree K k = D.degree k.1

/-- Target identifying the field image as the image of its underlying subgroup. -/
def fieldImage_eq_mapStatement (D : DegreeData G) (K : ClosedSubgroup G) : Prop :=
  D.fieldImage K = K.toSubgroup.map D.degree.toMonoidHom

/-- Target for the membership criterion in field inertia. -/
def mem_fieldInertia_iffStatement (D : DegreeData G) (K : ClosedSubgroup G)
    (g : G) : Prop :=
  g ∈ D.fieldInertia K ↔ g ∈ K ∧ D.degree g = 1

/-- Target for the membership criterion in internal field inertia. -/
def mem_fieldInertiaWithin_iffStatement (D : DegreeData G) (K : ClosedSubgroup G)
    (k : K.toSubgroup) : Prop :=
  k ∈ D.fieldInertiaWithin K ↔ D.degree k.1 = 1

/-- Target for the cardinality interpretation of the actual residue quotient. -/
def residueDegreeCardinal_eq_mk_residueQuotientStatement
    (D : DegreeData G) (K : ClosedSubgroup G) : Prop :=
  D.residueDegreeCardinal K = Cardinal.mk (D.residueQuotient K)

/-- Target for the absolute residue degree of the base field. -/
def residueDegreeCardinal_baseFieldStatement (D : DegreeData G) : Prop :=
  D.residueDegreeCardinal (baseField G) = 1

end DegreeData

end
end Langlands.NYLL.ClassFormation
