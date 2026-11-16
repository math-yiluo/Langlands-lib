/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.ValuationContinuity.Statements

/-!
# The defining kernel equation for the unramified degree subgroup

Modified by Worker 209: extract NYLL M301.003, prefix its namespace with
Langlands.NYLL, import the published target, and express the theorem's type
as that target with the complete source telescope. The source `rfl` proof
is unchanged. See the paired Markdown and licenses/NYLL/LICENSE and NOTICE.
-/

noncomputable section

namespace Langlands.NYLL.ClassFormation

universe u

namespace DegreeData

/-- The defining kernel equation for the reduction subgroup. -/
theorem unramifiedDegreeKernelWithin_eq_ker {G : Type u} [Group G] [TopologicalSpace G]
    (D : DegreeData G) (K : FiniteResidueAbstractField D) (f : ℕ) (hf : 0 < f) :
    unramifiedDegreeKernelWithin_eq_kerStatement D K f hf := by
  rfl

end DegreeData

end Langlands.NYLL.ClassFormation
