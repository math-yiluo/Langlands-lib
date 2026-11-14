/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
Modified by Worker 205, 2026-11-13: extract M266.020 from commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL and replace the source imports by the focused published
surjectivity and kernel-equality proofs below. The definition and its
universe, parameters and hypotheses are unchanged.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U008.Proofs
import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup.U018.Proofs

/-!
# The unramified norm quotient as a valuation quotient

Source: M266.020, lines 201–210 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`.
-/

noncomputable section

universe u

namespace Langlands.NYLL.LocalClassFieldTheory

/-- The valuation quotient model
`Kˣ / {x | n ∣ v(x)} ≃ Z/nZ`, in multiplicative notation. -/
noncomputable def unramifiedNormQuotientEquivZMod (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) :
    Kˣ ⧸ unramifiedNormSubgroup K n ≃* Multiplicative (ZMod n) :=
  (QuotientGroup.quotientMulEquivOfEq
    (unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom K n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (valuationModDegreeMulHom K n)
      (valuationModDegreeMulHom_surjective K n))

end Langlands.NYLL.LocalClassFieldTheory
