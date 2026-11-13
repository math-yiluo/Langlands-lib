/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions

/-!
# The NYLL finite-residue abstract-field data

Modified by Worker 120: extract M010.021–025 from the pinned Fields.lean,
prefix the namespace, name the anonymous finite-quotient instance
PortInternal.M010.d024, and use the focused published initial-data import.
The source bundle, parameters, instances and positive-degree body are retained.
See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

/-- An abstract field together with finiteness of its actual degree-image
quotient.  Its numerical residue degree is therefore genuinely positive. -/
structure FiniteResidueAbstractField (D : DegreeData G) where
  /-- The closed subgroup representing the abstract field. -/
  field : ClosedSubgroup G
  /-- The field's residue quotient is finite. -/
  finiteResidueQuotient : Finite (D.residueQuotient field)

namespace FiniteResidueAbstractField

variable {D : DegreeData G}

/-- Bundle a field at the boundary where its actual residue quotient is known
to be finite. -/
def ofField (D : DegreeData G) (K : ClosedSubgroup G)
    [hfinite : Finite (D.residueQuotient K)] :
    FiniteResidueAbstractField D where
  field := K
  finiteResidueQuotient := hfinite

/-- The underlying subgroup. -/
@[implicit_reducible]
def toSubgroup (K : FiniteResidueAbstractField D) : Subgroup G :=
  K.field.toSubgroup

/-- A finite-residue abstract field supplies finiteness of its residue quotient. -/
instance _root_.Langlands.NYLL.PortInternal.M010.d024
    (K : FiniteResidueAbstractField D) :
    Finite (D.residueQuotient K.field) :=
  K.finiteResidueQuotient

/-- The positive absolute residue degree. -/
noncomputable def residueDegree (K : FiniteResidueAbstractField D) : ℕ+ := by
  letI : Nonempty (D.residueQuotient K.field) := ⟨QuotientGroup.mk 1⟩
  exact ⟨Nat.card (D.residueQuotient K.field), Nat.card_pos⟩

end FiniteResidueAbstractField
end DegreeData

end
end Langlands.NYLL.ClassFormation
