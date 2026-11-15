/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 464, 2026-11-15: extract the M353.004 proof
(source degreeIndexList_nodup, lines 57–60) under the public port-internal name
Langlands.NYLL.PortInternal.M353.d004, prove the published Prop target
d004Statement, import the published Statements module, and replace the
source's simp call by a direct application of Finset.nodup_toList.
See the paired Markdown. Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DegreeIndexList.Statements

/-! # The fixed-degree monomial enumeration has no repetitions -/

noncomputable section

universe w

namespace Langlands.NYLL.PortInternal.M353

variable {sigma : Type w} [Fintype sigma]

/-- The fixed-degree enumeration has no repeated exponent vectors. -/
theorem d004 (m : ℕ) : d004Statement (sigma := sigma) m := by
  unfold d004Statement d003
  exact Finset.nodup_toList _

end Langlands.NYLL.PortInternal.M353

end
