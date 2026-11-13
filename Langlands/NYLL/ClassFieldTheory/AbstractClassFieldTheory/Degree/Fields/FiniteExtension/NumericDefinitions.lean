/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.Definitions
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.U081.Proofs
import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteExtension.U082.Proofs

/-!
# NYLL M010: positive relative residue and ramification data

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

/-- The residue coset type of a finite extension is finite.  This is derived
from the cardinal fundamental identity, rather than from a natural-valued
index whose infinite case would be represented by zero. -/
noncomputable instance residueQuotientFinite (D : DegreeData G) :
    Finite
      (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
        (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (E.base.toSubgroup.map D.degree.toMonoidHom)) := by
  apply Cardinal.lt_aleph0_iff_finite.mp
  simpa [Langlands.NYLL.PortInternal.M010.d081Statement,
    AbstractExtension.relativeResidueDegreeCardinal,
    relativeIndexCardinal, intersectionIndexCardinal] using
      Langlands.NYLL.PortInternal.M010.d081 E D

/-- The inertia coset type of a finite extension is finite.  As for the
residue quotient, this is a consequence of the cardinal fundamental identity. -/
noncomputable instance ramificationQuotientFinite (D : DegreeData G) :
    Finite
      (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
        (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
          (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)) := by
  apply Cardinal.lt_aleph0_iff_finite.mp
  simpa [Langlands.NYLL.PortInternal.M010.d082Statement,
    AbstractExtension.relativeRamificationIndexCardinal,
    relativeIndexCardinal, intersectionIndexCardinal] using
      Langlands.NYLL.PortInternal.M010.d082 E D

/-- The positive relative residue degree of a finite abstract extension. -/
def residueDegree (D : DegreeData G) : ℕ+ :=
  ⟨Nat.card
      (↥(E.base.toSubgroup.map D.degree.toMonoidHom) ⧸
        (E.field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
          (E.base.toSubgroup.map D.degree.toMonoidHom)),
    Nat.card_pos⟩

/-- The positive relative ramification index of a finite abstract extension. -/
def ramificationIndex (D : DegreeData G) : ℕ+ :=
  ⟨Nat.card
      (↥(E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker) ⧸
        (E.field.toSubgroup ⊓ D.degree.toMonoidHom.ker).subgroupOf
          (E.base.toSubgroup ⊓ D.degree.toMonoidHom.ker)),
    Nat.card_pos⟩

end FiniteAbstractExtension
end DegreeData

end
end Langlands.NYLL.ClassFormation
