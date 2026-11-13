/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Statements

/-!
# NYLL M010.026: the natural value of the positive residue degree

Modified by Worker 188: extract M010.026 from the pinned NYLL Fields
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

/-- The natural value of the positive residue degree is the quotient's `Nat.card`. -/
theorem residueDegree_coe (K : FiniteResidueAbstractField D) :
    residueDegree_coeStatement K :=
  rfl

end FiniteResidueAbstractField

end DegreeData

end
end Langlands.NYLL.ClassFormation
