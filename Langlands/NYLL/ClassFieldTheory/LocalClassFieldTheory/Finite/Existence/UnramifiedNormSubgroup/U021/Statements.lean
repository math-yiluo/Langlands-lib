/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 205, 2026-11-13: extract the indicated M266 source unit
from commit fbd320cd8b1b06487c58227e92eb135794267709, add the namespace
prefix, and use focused adapted imports. The statement is closed under
its original telescope; the proof uses that named proposition target.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U020.Definitions

/-! # Computation target for the unramified norm quotient equivalence -/

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The quotient equivalence sends a unit class to its reduced valuation. -/
def unramifiedNormQuotientEquivZMod_mkStatement : Prop :=
  ∀ (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (x : Kˣ),
    unramifiedNormQuotientEquivZMod K n (QuotientGroup.mk x) =
      valuationModDegreeMulHom K n x

end Langlands.NYLL.LocalClassFieldTheory
