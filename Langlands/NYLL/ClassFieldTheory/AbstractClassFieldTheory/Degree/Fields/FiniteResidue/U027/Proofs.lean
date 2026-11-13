/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Statements

/-!
# NYLL M010.027: the finite residue cardinal as a natural cardinal

Modified by Worker 188: extract M010.027 from the pinned NYLL Fields
source, prefix the namespace with Langlands.NYLL, use focused published
imports, and state the result using the exact named target. The source
proof route is retained. See the paired Markdown and licenses/NYLL/LICENSE
and NOTICE for the complete modification and attribution record.
-/

namespace Langlands.NYLL.ClassFormation

noncomputable section

universe u

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace DegreeData

namespace FiniteResidueAbstractField

variable {D : DegreeData G}

/-- Cardinal-to-positive-natural specialization at the finite boundary. -/
theorem residueDegreeCardinal_eq_coe (K : FiniteResidueAbstractField D) :
    residueDegreeCardinal_eq_coeStatement K := by
  change Cardinal.mk (D.residueQuotient K.field) =
    (Nat.card (D.residueQuotient K.field) : Cardinal)
  exact Nat.cast_card.symm

end FiniteResidueAbstractField

end DegreeData

end
end Langlands.NYLL.ClassFormation
