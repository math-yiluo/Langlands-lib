/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 194 (2026-11-14): extract the listed M114 units
from Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/CohomologyBridge.lean
at fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace/imports and theorem statements
as documented in the paired Markdown. Source construction bodies are retained.
Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Mathlib.LinearAlgebra.Quotient.Basic

namespace Langlands.NYLL.PortInternal.M114

noncomputable section

/-- Source M114.003: original construction. -/
def d003
    {A M : Type} [AddCommGroup A] [AddCommGroup M]
    (e : A ≃+ M) (N : Submodule ℤ M) : A →+ M ⧸ N :=
  N.mkQ.toAddMonoidHom.comp e.toAddMonoidHom

end

end Langlands.NYLL.PortInternal.M114
