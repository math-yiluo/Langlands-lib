/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 544, 2026-11-14: extract M313.004 from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709, prefix the namespace with
Langlands.NYLL, and replace the source imports with focused Mathlib imports.
Omit unused section variables and local instances; retain the defining body.
Retained license and notices: licenses/NYLL/.
-/

import Mathlib.Data.ENat.Defs
import Mathlib.Basic.Real.Basic

/-!
# Extended-natural truncation at a real bound

The pure truncation function from NYLL's ramification-number formula.
It has no field or valuation parameters.
-/

noncomputable section

namespace Langlands.NYLL.RamificationTheory.HilbertRamification.Higher

/-- `min {i,r}`, with the extended value `infinity` truncated to `r`. -/
def truncateENatAtDVF (i : ℕ∞) (r : ℝ) : ℝ :=
  ENat.recTopCoe r (fun n => min (n : ℝ) r) i

end Langlands.NYLL.RamificationTheory.HilbertRamification.Higher
