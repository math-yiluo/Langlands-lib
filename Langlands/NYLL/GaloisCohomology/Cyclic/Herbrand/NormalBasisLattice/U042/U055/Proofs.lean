/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 641 on 2026-11-14: extracted this proof into the
Langlands.NYLL namespace and made its exact published Statement the theorem
type. The paired Markdown records the proof and adaptations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U006.Proofs

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
variable [ValuativeRel K]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] in
private theorem baseUniformizer_image_in_maximalIdeal :
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K) ∈
      (𝓂[L] : Ideal 𝒪[L]) := by
  have hπK :
      chosenIntegerRingUniformizer K ∈ (𝓂[K] : Ideal 𝒪[K]) := by
    rw [chosenIntegerRingUniformizer_maximalIdeal_eq K]
    exact Ideal.subset_span (Set.mem_singleton (chosenIntegerRingUniformizer K))
  exact (Valuation.HasExtension.algebraMap_mem_maximalIdeal_iff
    (ValuativeRel.valuation K) (ValuativeRel.valuation L)).2 hπK

omit [FiniteDimensional K L] [IsGalois K L] in
theorem chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmodule
    {N : Submodule 𝒪[K] L} {b : Nat}
    (hb : chosenBaseUniformizerPowSubmodule K L b N ≤ integerRingFieldSubmodule K L) :
    chosenBaseUniformizerPowSubmodule_succ_le_maximalIdealFieldSubmodule_of_le_integerRingFieldSubmoduleStatement
      K L hb := by
  intro x hx
  rcases hx with ⟨y, hyN, rfl⟩
  have hby_int :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y ∈ 𝒪[L] :=
    hb ⟨y, hyN, rfl⟩
  let z : 𝒪[L] :=
    ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y, hby_int⟩
  let πL : 𝒪[L] :=
    integerRingMapOfValuationExtension K L (chosenIntegerRingUniformizer K)
  have hπL : πL ∈ (𝓂[L] : Ideal 𝒪[L]) :=
    baseUniformizer_image_in_maximalIdeal K L
  refine ⟨πL * z, Ideal.mul_mem_right z _ hπL, ?_⟩
  dsimp [πL, z]
  change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K) *
      (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ b) * y) =
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (b + 1)) * y
  simp [pow_add, map_mul, mul_comm, mul_left_comm]

end
end Langlands.NYLL.CyclicCohomology
