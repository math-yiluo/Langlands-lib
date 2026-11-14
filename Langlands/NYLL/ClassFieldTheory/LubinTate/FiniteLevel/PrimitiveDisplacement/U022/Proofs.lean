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

theorem d022
    (hπ : F.toCompleteDVF.valuation.IsUniformizer (π : K))
    (a : F.valuationSubringˣ) (k : ℕ)
    (ha : a ∈ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF k)
    (hnot : a ∉ CompleteDVF.higherPrincipalUnitGroup F.toCompleteDVF (k + 1)) :
    d022Statement hπ a k ha hnot := by
  change ∃ c : F.valuationSubringˣ,
    (a : F.valuationSubring) - 1 = (c : F.valuationSubring) * π ^ k
  change (a : F.valuationSubring) - 1 ∈ F.toCompleteDVF.maximalIdeal ^ k at ha
  change (a : F.valuationSubring) - 1 ∉ F.toCompleteDVF.maximalIdeal ^ (k + 1) at hnot
  have hspan : F.toCompleteDVF.maximalIdeal = Ideal.span {π} := hπ.is_generator
  have hdiv : π ^ k ∣ (a : F.valuationSubring) - 1 := by
    rwa [hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at ha
  rcases hdiv with ⟨c, hc⟩
  have hcnot : c ∉ F.toCompleteDVF.maximalIdeal := by
    intro hcmem
    apply hnot
    rw [hc]
    have hpowmem : π ^ k ∈ F.toCompleteDVF.maximalIdeal ^ k := by
      simpa only [hspan, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
        using (dvd_rfl : π ^ k ∣ π ^ k)
    simpa only [pow_succ] using Ideal.mul_mem_mul hpowmem hcmem
  have hcunit : IsUnit c := IsLocalRing.notMem_maximalIdeal.mp hcnot
  rcases hcunit with ⟨cunit, rfl⟩
  refine ⟨cunit, ?_⟩
  simpa only [mul_comm] using hc

end Langlands.NYLL.PortInternal.M362
