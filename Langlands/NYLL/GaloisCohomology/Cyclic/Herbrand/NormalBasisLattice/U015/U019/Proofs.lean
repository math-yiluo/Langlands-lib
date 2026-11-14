/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 516 on 2026-11-14: ported M144.019 to the
Langlands.NYLL namespace and proved the published Statement target.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.Statements

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u
open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- Each successive chosen uniformizer-power submodule lies in the preceding one. -/
theorem chosenBaseUniformizerPowSubmodule_succ_le
    (n : Nat) (N : Submodule 𝒪[K] L) :
    chosenBaseUniformizerPowSubmodule_succ_leStatement K L n N := by
  unfold chosenBaseUniformizerPowSubmodule_succ_leStatement
  intro x hx
  change ∃ y : L, y ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (n + 1)) * y = x at hx
  rcases hx with ⟨y, hyN, rfl⟩
  change ∃ z : L, z ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * z =
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (n + 1)) * y
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K) * y, ?_, ?_⟩
  · simpa [Algebra.smul_def] using
      N.smul_mem (chosenIntegerRingUniformizer K) hyN
  · simp [pow_succ, map_mul, mul_assoc]

end
end Langlands.NYLL.CyclicCohomology
