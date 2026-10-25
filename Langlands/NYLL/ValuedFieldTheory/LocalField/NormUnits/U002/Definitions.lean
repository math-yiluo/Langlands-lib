/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 25 October 2026:
Extract only M092.002 from Nyll/ValuedFieldTheory/LocalField/NormUnits.lean
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, omit the unused universe w and all other declarations,
and retain the original Mathlib-only import and definition body.
The upstream LICENSE and NOTICE are preserved in licenses/NYLL/.
-/

import Mathlib.RingTheory.Norm.Transitivity

/-!
# Field norm on unit groups

The algebra norm restricted to units, with no finite-dimensionality assumption.
-/

namespace Langlands.NYLL.LocalFieldTheory

noncomputable section

universe u v

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- The algebra norm, restricted to unit groups. -/
def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

end

end Langlands.NYLL.LocalFieldTheory
