/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueAlgebraicClosureDegree.Initial.Statements

/-!
# Finite local reciprocity: degree of the embedded finite subextensions (proof)

Modified by Worker 46: prove the published target
`Langlands.NYLL.LocalClassFieldTheory.finrank_finiteResidueGaloisIntermediateFieldInStatement`
(M236.009) under the source theorem name in the `Langlands.NYLL` namespace,
under the source's `variable` blocks and its `omit [Algebra.IsAlgebraic k Omega]`.
The source proof is kept; the characteristic-prime instance of the source's
private `finiteResidueBaseRingCharPrime` (M236.001) is supplied by a local
`have` in the proof. The source `@[simp]` attribute is kept. See the paired Markdown and
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section

universe u v

open CategoryTheory Opposite
open FiniteGaloisIntermediateField ProfiniteGrp
open Polynomial

variable (k : Type u) [Field k] [Fintype k]
variable (Omega : Type v) [Field Omega] [Algebra k Omega]
  [Algebra.IsAlgebraic k Omega] [IsAlgClosed Omega]

omit [Algebra.IsAlgebraic k Omega] in
/-- The embedded degree-`n` finite Galois intermediate field has degree `n`
over `k` (M236.009). -/
@[simp]
theorem finrank_finiteResidueGaloisIntermediateFieldIn
    (n : ℕ) [NeZero n] :
    finrank_finiteResidueGaloisIntermediateFieldInStatement k Omega n := by
  have : Fact (ringChar k).Prime := ⟨CharP.char_is_prime k (ringChar k)⟩
  calc
    Module.finrank k
        (finiteResidueGaloisIntermediateFieldIn k Omega n) =
        Module.finrank k
          (FiniteField.Extension k (ringChar k) n) :=
      (finiteResidueExtensionEquivIntermediateIn k Omega n).toLinearEquiv.finrank_eq.symm
    _ = n := FiniteField.finrank_extension k (ringChar k) n

end
end Langlands.NYLL.LocalClassFieldTheory
