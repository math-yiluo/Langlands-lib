/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.GaloisSubextension.Statements

/-!
# NYLL M010.061: evaluation of the named galois quotient projection

Modified by Worker 188: extract M010.061 from the pinned NYLL Fields
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

namespace GaloisSubextension

variable {K : ClosedSubgroup G}

/-- The named quotient projection agrees with `QuotientGroup.mk` under its comparison. -/
theorem extensionQuotientMk_apply (L : GaloisSubextension K) (k : K.toSubgroup) :
    extensionQuotientMk_applyStatement L k :=
  rfl

end GaloisSubextension

end DegreeData

end
end Langlands.NYLL.ClassFormation
