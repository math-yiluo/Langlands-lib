/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 331, 2026-11-14: extract M353.004–005 as exact Prop-valued Statement targets,
use the public port-internal names and focused d003 import, and omit the
proofs, unrelated source units and ineffective local-field parameters.
See the paired Markdown. Original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.RecursiveIntertwiner.DegreeIndexList.Definitions

/-! # Targets for fixed-degree monomial enumeration -/

noncomputable section

universe w

namespace Langlands.NYLL.PortInternal.M353

variable {sigma : Type w} [Fintype sigma]

/-- The fixed-degree enumeration has no repeated exponent vectors. -/
def d004Statement (m : ℕ) : Prop :=
  (d003 (sigma := sigma) m).Nodup

/-- Every exponent vector of total degree `m` appears in its enumeration. -/
def d005Statement
    (m : ℕ) (d : {d : sigma →₀ ℕ // d.degree = m}) : Prop :=
  d ∈ d003 (sigma := sigma) m

end Langlands.NYLL.PortInternal.M353

end
