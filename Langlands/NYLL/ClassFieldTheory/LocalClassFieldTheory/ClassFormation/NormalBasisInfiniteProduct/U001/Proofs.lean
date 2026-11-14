/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

-- Modified by Worker 519: extract M150.001 from NYLL fbd320cd,
-- prefix the namespace, state the exact published target, and inline the
-- definitional membership bridges and uniformizer maximal-ideal argument.
-- See Proofs.md and licenses/NYLL/ for provenance and licensing.

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisInfiniteProduct.LatticeBoundStatements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U006.Proofs

namespace Langlands.NYLL.LocalClassFieldTheory

noncomputable section
universe u
open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

theorem chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_pow
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [ValuativeRel L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    (m : Nat) {x : L}
    (hx : x ∈ chosenBaseUniformizerPowSubmodule K L m
      (integerRingFieldSubmodule K L)) :
    chosenBaseUniformizerPow_integerRingFieldSubmodule_exists_mem_maximalIdeal_powStatement
      K L m hx := by
  rcases hx with ⟨y, hy, rfl⟩
  let yInt : 𝒪[L] := ⟨y, hy⟩
  let πL : 𝒪[L] :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπK : chosenIntegerRingUniformizer K ∈ (𝓂[K] : Ideal 𝒪[K]) := by
    rw [chosenIntegerRingUniformizer_maximalIdeal_eq K]
    exact Ideal.subset_span (Set.mem_singleton (chosenIntegerRingUniformizer K))
  have hπL : πL ∈ (𝓂[L] : Ideal 𝒪[L]) :=
    (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff
      (ValuativeRel.valuation K) (ValuativeRel.valuation L)).2 hπK
  refine ⟨πL ^ m * yInt, ?_, ?_⟩
  · exact Ideal.mul_mem_right yInt _ (Ideal.pow_mem_pow hπL m)
  · dsimp [πL, yInt, baseIntegerScalarMulLinearMap]
    rw [map_pow]
    rfl

end
end Langlands.NYLL.LocalClassFieldTheory
