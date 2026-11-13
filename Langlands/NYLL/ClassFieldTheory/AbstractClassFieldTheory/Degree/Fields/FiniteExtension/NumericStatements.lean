/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.NumericDefinitions

/-!
# NYLL M010: finite relative residue and ramification targets

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

namespace FiniteAbstractExtension

variable (E : FiniteAbstractExtension G)

def residueDegree_coeStatement (D : DegreeData G) : Prop :=
  (E.residueDegree D : ℕ) =
      Nat.card
        (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
          (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
            (E.base.toSubgroup.map D.degree.toMonoidHom))

def ramificationIndex_coeStatement (D : DegreeData G) : Prop :=
  (E.ramificationIndex D : ℕ) =
      Nat.card
        (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
          (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
            (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker))

def mapped_relIndex_eq_residueDegreeStatement (D : DegreeData G) : Prop :=
  (E.field.toSubgroup.map D.degree.toMonoidHom).relIndex
        (E.base.toSubgroup.map D.degree.toMonoidHom) =
      (E.residueDegree D : ℕ)

def inertia_relIndex_eq_ramificationIndexStatement (D : DegreeData G) : Prop :=
  (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).relIndex
        (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) =
      (E.ramificationIndex D : ℕ)

def degree_eq_residueDegree_mul_ramificationIndexStatement (D : DegreeData G) : Prop :=
  (E.degree : ℕ) =
      (E.residueDegree D : ℕ) * (E.ramificationIndex D : ℕ)

def ramificationIndex_eq_one_of_isUnramifiedStatement (D : DegreeData G)
    (hE : E.IsUnramified D) : Prop :=
  (E.ramificationIndex D : ℕ) = 1

def residueDegree_eq_one_of_isTotallyRamifiedStatement (D : DegreeData G)
    (hE : E.IsTotallyRamified D) : Prop :=
  (E.residueDegree D : ℕ) = 1

def residueDegree_eq_degree_of_isUnramifiedStatement (D : DegreeData G)
    (hE : E.IsUnramified D) : Prop :=
  (E.residueDegree D : ℕ) = (E.degree : ℕ)

def relativeResidueDegreeCardinal_eq_coeStatement (D : DegreeData G) : Prop :=
  E.toAbstractExtension.relativeResidueDegreeCardinal D =
      ((E.residueDegree D : ℕ) : Cardinal)

end FiniteAbstractExtension
end DegreeData

end
end Langlands.NYLL.ClassFormation
