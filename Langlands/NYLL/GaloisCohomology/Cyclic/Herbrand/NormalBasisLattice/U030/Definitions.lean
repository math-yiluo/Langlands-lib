/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 231 on 2026-11-13: extracted the source units recorded
in the paired Markdown; prefixed the namespace with Langlands.NYLL and
reduced imports. Source data bodies and parameter binding are preserved.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Mathlib.FieldTheory.Galois.NormalBasis
import Mathlib.NumberTheory.LocalField.Basic

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

variable [ValuativeRel K]

variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional K L] [IsGalois K L] in
/-- The finite inverse-correction sum
`(-x) + (-x)^2 + ... + (-x)^d`.

When `x` is topologically nilpotent and the lattice is complete, these are the
finite approximations to `(1+x)⁻¹ - 1`. -/
def inverseCorrectionPartialSum (x : L) (d : Nat) : L :=
  (Finset.range d).sum fun i => (-x) ^ (i + 1)

end
end Langlands.NYLL.CyclicCohomology
