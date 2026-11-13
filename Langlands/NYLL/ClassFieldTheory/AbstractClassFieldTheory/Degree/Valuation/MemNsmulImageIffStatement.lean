/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Valuation.Definitions

/-!
# Membership in the natural-multiple image

Modified by Worker 192: extract the statement of M025.005 from the pinned NYLL
source, prefix the namespace with `Langlands.NYLL`, and replace the theorem by
a Prop-valued definition with suffix `Statement`. Its proof and simp attribute
belong to a separate proof contribution. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.ClassFormation

/-- An element belongs to the natural-multiple image exactly when it has a
preimage in the subgroup. -/
def mem_nsmulImage_iffStatement (Z : AddSubgroup ZHat) (n : ℕ) (z : ZHat) : Prop :=
  z ∈ nsmulImage Z n ↔ ∃ x ∈ Z, n • x = z

end Langlands.NYLL.ClassFormation
