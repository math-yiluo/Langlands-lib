/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 299, 2026-11-13: prove the extracted exact target using
Mathlib's uniformizer generator and ideal APIs rather than the source's
intermediate CompleteDVF wrappers; qualify the private source name under
Langlands.NYLL.PortInternal.M362. The retained license and notices are in
licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FiniteLevel.PrimitiveDisplacement.PrincipalDepth.Statements
import Mathlib.Algebra.GroupWithZero.Divisibility

noncomputable section

universe u v

namespace Langlands.NYLL.PortInternal.M362

open Langlands.NYLL.LocalFieldTheory.DiscreteValuationField

variable {K : Type u} [Field K]
variable {F : LocalField.{u, v} K} {π : F.valuationSubring}

theorem d026
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a c : F.valuationSubringˣ) (r k : ℕ)
    (hsub : (a : F.valuationSubring) - 1 =
      (c : F.valuationSubring) * π ^ r) :
    d026Statement hπ a c r k hsub := by
  change ((a : F.valuationSubring) - 1 ∈ F.toCompleteDVF.maximalIdeal ^ k) ↔ k ≤ r
  have hspan : F.toCompleteDVF.maximalIdeal = Ideal.span {π} := hπ.is_generator
  have hπ0 : π ≠ 0 := by
    intro hzero
    apply hπ.ne_zero
    simpa using congrArg (fun x : F.valuationSubring => (x : K)) hzero
  rw [hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton, hsub,
    c.isUnit.dvd_mul_left]
  exact pow_dvd_pow_iff hπ0 hπ.not_isUnit

end Langlands.NYLL.PortInternal.M362
