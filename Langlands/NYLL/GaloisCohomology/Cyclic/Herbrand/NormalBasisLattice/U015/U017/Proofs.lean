/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 516 on 2026-11-14: ported M144.017 to the
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

/-- Increasing the exponent preserves membership after scalar multiplication. -/
theorem chosenBaseUniformizerPow_mul_mem_mono
    {M : Submodule 𝒪[K] L} {m n : Nat} {x : L} (hmn : m ≤ n)
    (hx : algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * x ∈ M) :
    chosenBaseUniformizerPow_mul_mem_monoStatement K L hmn hx := by
  unfold chosenBaseUniformizerPow_mul_mem_monoStatement
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
  rw [hd]
  have hscaled :
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) *
          (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * x) ∈ M := by
    simpa [Algebra.smul_def, mul_assoc] using
      M.smul_mem (chosenIntegerRingUniformizer K ^ d) hx
  simpa [pow_add, map_mul, mul_assoc, mul_comm, mul_left_comm] using hscaled


end
end Langlands.NYLL.CyclicCohomology
